# NI Testing Framework — Architecture

How the non-interference (NI) testing framework on top of Vellvm is put
together. For hands-on CLI usage of each flag, see
[NI_TESTING.md](NI_TESTING.md).

## The three pieces

```
                    generator
                        │
                        ▼
                  random program
                    ┌───┴───┐
                    ▼       ▼
            taint tracker   NI tester
            (partition       (executes the
             discovery)       program, emits
                              the observation
                              trace)
                    ▼       ▼
                    cross-check
            ─────────────────────────────────
            pick any var x in the complement
              of TOBS_REGS → vary x across
              two runs → traces must match
```

Each piece is independent and exercisable on its own.

| Piece | What it does | Trusted? | Driver flag |
|---|---|---|---|
| **Generator** | Samples a random LLVM program | — | (Rocq side; not driven from CLI) |
| **NI tester** | Runs the program, emits the observation trace | **ground truth** | `-interpret-obs-args` |
| **Taint tracker** | Outputs the public partition | **under test** | `-taint-track-args` |

The QC harness composes all three. Property: every register / memory
identity outside `TOBS_REGS ∪ TOBS_ADDRS` can be varied without changing
the trace.

---

## (1) Generator — random LLVM programs

Pure Rocq, lives in QuickChick land. Produces parsed LLVM ASTs.

**Entry points** (in [rocq/QC/GenAST.v](rocq/QC/GenAST.v)):

- `gen_llvm` — `main` takes no args.
- `gen_llvm_with_args` — `main(i32, …)` with 1–4 random i32 args.
- `gen_llvm_with_secret` — `main(i32 %secret)`, may have helper functions.
- `gen_llvm_with_secret_nofun` — `main(i32 %secret)`, **no** helper
  functions. Required for the partition-style taint tracker because
  `denote_function_taint` does not yet handle inter-procedural calls
  (`CallE`).

`gen_PROG_*` wrappers live in
[rocq/QC/NITests.v](rocq/QC/NITests.v).

---

## (2) NI tester — the observation pipeline

For NI we don't need full execution semantics, just a stream of
*public observations*: which addresses were loaded/stored, and which
way each conditional branch went. Two runs with different secrets must
produce identical observation streams; otherwise a secret has leaked.

The instrumentation is bolted onto Vellvm's standard interpretation
stack at **L2** — the unique layer where both `MemoryE` (Load/Store)
and `DebugE` (branch direction) still live in the event signature.

### Pipeline

```
denote_function (or denote_function_taint)
        │
        ▼
interp_intrinsics → interp_global → interp_local_stack
                                      (L2)
                                        ↓
                                   observe_L2          ← instrumentation
                                        ↓
                                interp_memory → exec_undef → L4
```

`observe_L2` walks the L2 itree, re-emits every event unchanged, and
appends a `Z` to its `obs : list Z` whenever `event_obs` matches a
Load/Store/DebugBranch.

**`event_obs`** ([InterpretationStack.v](rocq/Semantics/InterpretationStack.v) — `event_obs`):

```coq
match e with
| Load _ (DVALUE_Addr a)           => Some (LP.PTOI.ptr_to_int a)
| Store _ (DVALUE_Addr a) _        => Some (Z.opp (LP.PTOI.ptr_to_int a))
| DebugBranch true                 => Some 1000000%Z
| DebugBranch false                => Some 1000001%Z
| _                                => None
end.
```

### Branch event mechanism

Branch direction is not a native LLVM event. We piggyback on `DebugE`
in [rocq/Semantics/LLVMEvents.v](rocq/Semantics/LLVMEvents.v):

```coq
Variant DebugE : Type -> Type :=
| Debug       : unit -> DebugE unit
| DebugBranch : bool -> DebugE unit.
```

`DebugE` is the only event family already wired through every
interpretation layer with a no-op semantics, so adding a constructor
is a free extension. Emission happens in
[rocq/Semantics/Denotation.v](rocq/Semantics/Denotation.v) at the
`TERM_Br` terminator.

### OCaml entry

`interpret_with_args_obs` in
[src/ml/interpreter.ml](src/ml/interpreter.ml) — packs the int list
into a `uvalue list`, calls `TopLevelBigIntptr.interpreter_gen_obs`,
and steps the resulting itree, extracting `(obs, dvalue)` from the
nested result tuple.

---

## (3) Taint tracker — partition-style

The tracker has **only one layer** in this refactor (the prior Layer 1
/ static AST analysis was dropped). It operates as a taint-augmented
denotation that runs alongside the standard one and threads a
`tstate` through every instruction.

### Source alphabet

```coq
Definition taint_src : Type := (raw_id + Z)%type.
Definition taint     : Type := list taint_src.
```

A taint set carries:
- `inl id` — an SSA register named `id`
- `inr addr` — a memory cell at concrete address `addr`

### Self-tagging via lookup default

Every SSA variable and every memory cell is its own source. Rather
than seeding identities at definition / allocation time everywhere,
the trick is centralised in two lookup helpers in
[rocq/NI/TaintTracker.v](rocq/NI/TaintTracker.v):

```coq
Definition treg_lookup tr id : taint :=
  join_taints [inl id] (treg_lookup_raw tr id).

Definition tmem_lookup tm addr : taint :=
  join_taints [inr addr] (tmem_lookup_raw tm addr).
```

Every read of an SSA name picks up that name's identity; every read of
a memory cell picks up the cell's address. The "every variable / cell
is its own source" semantics drops out of these two `join_taints`
calls — no per-definition seeding needed.

### tstate and the partition output

```coq
Record tstate := mk_tstate {
  ts_tpc   : taint;     (* PC taint *)
  ts_tregs : treg_map;  (* register taint map *)
  ts_tobs  : taint;     (* the public partition *)
  ts_tmem  : tmem_map   (* memory taint map *)
}.

Fixpoint split_taint (t : taint) : (list raw_id * list Z) := …
```

`ts_tobs` accumulates source identities that flowed into an
observation event (a branch condition or a Load/Store address).
`split_taint` separates it into `(public regs, public addrs)` — what
the OCaml driver prints between the `TOBS_REGS_*` and `TOBS_ADDRS_*`
markers.

**Reading the output:** any source identity *not* in `ts_tobs` is
guaranteed not to affect the observation trace. That set is the
"safe to vary" partition.

### `denote_instr_taint`

Mirrors `denote_instr`'s `(instr_id * instr dtyp * list metadata)`
input shape. Two cases are duplicated to capture the concrete
address:

- **Load**: emits the same events as `denote_instr` (Load, LocalWrite),
  then computes `result_taint = ptr_taint ⊔ tmem_lookup(addr) ⊔ pc`
  and accumulates `ptr_taint ⊔ [inr addr] ⊔ pc` into `ts_tobs`.
- **Store**: emits Store, then updates `tmem[addr] := val_taint ⊔ pc`
  and accumulates `ptr_taint ⊔ [inr addr] ⊔ pc` into `ts_tobs`.

All other instruction kinds delegate to `denote_instr` and apply a
pure AST-only update via `taint_instr_pure` (Op, Alloca, Call, …).

### Pipeline composition (in OCaml)

`interpret_with_args_taint_obs` in
[src/ml/interpreter.ml](src/ml/interpreter.ml) wires together:

1. `TopLevelBigIntptr.build_global_environment`
2. `TaintTrackerBigIntptr.denote_function_taint` (returns `itree L0' (tstate * uvalue)`)
3. `Recursion.interp_mrec` (L0' → L0; the handler is trivial because
   `_nofun` programs emit no `CallE`)
4. `InterpreterStackBigIntptr.interp_mcfg4_exec_obs` (the obs pipeline
   shared with the plain interpreter)

Glued together with `Obj.magic` because Coq's extraction generates
non-unifying — but semantically isomorphic — `itree L0` types for
different module instantiations of `LP`/`MEM`.

---

## How the two pipelines share `interp_mcfg4_exec_obs`

```
plain NI:    denote_function          → itree L0 uvalue
                  │
Option B:    denote_function_taint    → itree L0' (tstate * uvalue)
                  │
             interp_mrec (no-op for nofun programs)
                  │
                  ▼
             interp_mcfg4_exec_obs    ← shared by both
                  │
                  ▼
             itree L4 (..., (obs, [tstate], uvalue))
```

Because `denote_instr_taint` emits the **same events** as
`denote_instr` (just with extra `tstate` threading), the observation
trace is identical between `-interpret-obs-args` and
`-taint-track-args` for the same input. The taint flag just adds the
partition.

---

## How the QC harness composes everything

Active property `vellvm_taint_soundness_partition` in
[rocq/QC/NITests.v](rocq/QC/NITests.v).

For each random `Prog`:

1. Find `main`'s first i32 parameter (its `raw_id`).
2. Run the tracker via `-taint-track-args 42` → get `TOBS_REGS`.
3. Run the plain interpreter via `-interpret-obs-args 42` and
   `-interpret-obs-args 137` → get two traces.
4. If `secret` is **in** `TOBS_REGS`: the tracker permits trace
   divergence; trivially accept.
5. If `secret` is **not in** `TOBS_REGS`: the tracker claims it's
   safe; the two traces must match. If they don't, the tracker is
   **unsound** — report counterexample.

A successful run on N samples means: no sampled program had
`secret ∉ TOBS_REGS` but actually-different traces.

### Shell-out, not in-process

The harness shells out to `./vellvm` because Coq extraction can't
directly call the pipeline (different `LP`/`MEM` instantiations
produce incompatible `itree L0` OCaml types). The framing markers
exist exactly to make the OCaml output parseable from inside the
Coq-side harness.

### Status

The Rocq side compiles and `make ni-tests` builds the test binary,
but automated invocation is currently blocked on an upstream regression
in `rocq/QC/QCVellvm.v` (`Cannot find module DV`, `L4` parameterisation
drift). Vanilla `make qc-tests` reproduces the same failure on a
fresh `origin/dev` checkout. Once upstream's `QCVellvm.v` is repaired,
`make ni-tests` will execute the property unchanged.

In the meantime the soundness check is exercised manually against the
fixtures in [../ni_examples/](../ni_examples/) — see
[NI_TESTING.md](NI_TESTING.md) for worked examples.

---

## Files of interest

| File | Role |
|---|---|
| [rocq/QC/GenAST.v](rocq/QC/GenAST.v) | Generators (`gen_llvm_with_secret_nofun`, …) |
| [rocq/QC/NITests.v](rocq/QC/NITests.v) | QC property + shell-out axioms |
| [rocq/Semantics/InterpretationStack.v](rocq/Semantics/InterpretationStack.v) | `event_obs`, `observe_L2`, `interp_mcfg4_exec_obs` |
| [rocq/Semantics/TopLevel.v](rocq/Semantics/TopLevel.v) | `interpreter_gen_obs` |
| [rocq/Semantics/LLVMEvents.v](rocq/Semantics/LLVMEvents.v) | `DebugE` + `DebugBranch` |
| [rocq/Semantics/Denotation.v](rocq/Semantics/Denotation.v) | `TERM_Br` emission |
| [rocq/NI/TaintTracker.v](rocq/NI/TaintTracker.v) | Partition-style taint tracker (~440 LOC) |
| [src/ml/interpreter.ml](src/ml/interpreter.ml) | OCaml entry points (`interpret_with_args_obs`, `interpret_with_args_taint_obs`) |
| [src/ml/driver.ml](src/ml/driver.ml) | CLI flag dispatch + framed output |
| [src/ml/main.ml](src/ml/main.ml) | Flag registration |

For per-flag CLI usage and worked examples, see
[NI_TESTING.md](NI_TESTING.md).
