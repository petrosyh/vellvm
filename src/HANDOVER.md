# NI Testing Framework Refactor — Session Handover

Self-contained context for a fresh Claude thread (or human collaborator)
to pick up this work on a different machine. Reads top to bottom; assumes
no prior conversation context.

## TL;DR (60-second summary)

The Vellvm NI (non-interference) testing framework was refactored from
a Layer-1+Layer-2 hybrid taint tracker into a single partition-style
design. The refactor exists on **two branches**:

| Branch | Base | `make qc-tests` | `make ni-tests` | Use for |
|---|---|---|---|---|
| `ni-refactoring`         | `origin/dev` (`f1ec3588`)  | ❌ blocked upstream | ❌ blocked upstream | future merge when upstream is repaired |
| `ni-refactoring-stable`  | fork point (`9557f168`)    | ✅ builds + runs    | ✅ **1000/1000 in 93 s** | **daily driver** |

Both branches contain the same partition-style design (`taint =
list (raw_id + Z)`, self-tagging via lookup defaults, output is the
public partition). The stable branch additionally has a working QC
test harness because the upstream rot (broken `QCVellvm.v` +
`ShowAST.v`) happened after our fork point.

The refactor commit on `ni-refactoring` is `35f58726`; on
`ni-refactoring-stable` it's `c0bf7d01`. Old branch `ni-taint-semantic`
(prior incremental work, layer-1+layer-2) is preserved at
`da039a52 "last commit before refactoring"` for reference.

---

## Project overview

**Vellvm** is a Coq verified LLVM IR semantics with an extracted OCaml
interpreter. This work adds a **non-interference (NI) testing
framework** on top of it:

- A **generator** (QuickChick) that produces random LLVM programs.
- An **NI tester** — the `./vellvm` binary with a flag that runs a
  program and emits an "observation trace" (Load/Store addresses +
  branch directions).
- A **taint tracker** that predicts which inputs/cells influence
  observations.
- A **QC harness** that cross-checks: pick a variable the tracker
  claims is safe, vary it across two runs, assert the observation
  traces match.

User contact: yonghyun.kim@sf.snu.ac.kr. Project sits in
`/home/yonghyunkim/works/vellvm/` (WSL2). Opam switch named
`vellvm`. The user previously did the layer-1+layer-2 incremental work
on `ni-taint-semantic`; this session was the partition-style refactor.

---

## What changed in this session

### Starting state

User came in on `ni-taint-semantic` (3274 LOC of additions across 27
files: a Layer-1 static taint tracker, a Layer-2 dynamic tracker, lots
of dead QC tests, three near-identical CLI-flag-handling functions).
They wanted to:

1. Clean up the accreted code (~80% reduction was achievable).
2. Switch from "designate sources, check if they leak" to "every var /
   cell is its own source, output the public partition directly."
3. Drop Layer 1 entirely.
4. Replace 5 CLI flags with 2.

### Design decisions made

**Partition-style taint analysis.** Each SSA register `x` and each
memory address `addr` is its own taint source (`taint = list (raw_id + Z)`).
The output `ts_tobs` is the **public partition** — the set of
identities that flowed into an observation event. The complement is
"safe to vary." Inspired by the user's earlier `SpecIBT-old` codebase,
which had the same alphabet (`reg_id + mem_addr`).

**Self-tagging via lookup defaults** (the trick that makes this clean):

```coq
Definition treg_lookup tr id : taint :=
  join_taints [inl id] (treg_lookup_raw tr id).

Definition tmem_lookup tm addr : taint :=
  join_taints [inr addr] (tmem_lookup_raw tm addr).
```

Every read of an SSA name picks up `[inl id]`; every read of a memory
cell picks up `[inr addr]`. No init-time seeding needed anywhere else.

**Observation events via `DebugBranch`-on-`DebugE`.** Branch
directions are not native LLVM events, so we piggyback on `DebugE`
(the only event family threaded through every interpretation layer
with no-op semantics). Adding `DebugBranch : bool -> DebugE unit` is
a free extension — only `observe_L2` does anything with it; every
existing interpreter / proof is unchanged. Emitted from `TERM_Br` in
`Denotation.v`. Picked up at L2 by `observe_L2` (cofixpoint) in
`InterpretationStack.v`.

**Two-flag CLI surface:**

| Flag | What it does |
|---|---|
| `-interpret-obs-args <n1,n2,...>` | Run program with i32 args; emit observation trace |
| `-taint-track-args <n1,n2,...>`   | Same + emit the public partition (TOBS_REGS + TOBS_ADDRS) |

Replaces the old branch's `-interpret-obs` / `-interpret-obs-secret`
/ `-interpret-obs-args` / `-taint-track` / `-taint-track-semantic`
accretion.

**Output framing:**
- `---OBS_TRACE_BEGIN---` / `---OBS_TRACE_END---` — one `Z` per line
- `---TOBS_REGS_BEGIN---` / `---TOBS_REGS_END---` — register names
- `---TOBS_ADDRS_BEGIN---` / `---TOBS_ADDRS_END---` — memory addresses

**Observation event encoding** (see `event_obs` in `InterpretationStack.v`):

| Value | Meaning |
|---|---|
| `n > 0, n < 1000000` | `OLoad(addr=n)` |
| `n < 0` | `OStore(addr=-n)` |
| `1000000` | `OBranch(true)` |
| `1000001` | `OBranch(false)` |

### Two-branch story

We initially built `ni-refactoring` on top of `origin/dev` (131 commits
ahead of the fork point), thinking forward-aligned was better. The
refactor compiled and the CLI flags worked, but `make qc-tests` /
`make ni-tests` failed.

Diagnosis (`git log` evidence):

- Commit `19206d18` "One pass of module refactoring. #421" on Mar 17
  2026: defunctorised `LLVMEvents`, made events polymorphic in
  `dvalue uvalue`, removed `LP.Events` submodule. Author's own commit
  message: *"There is still a lot of detangling / cleanup to do."*
  → `QCVellvm.v` references the old unparameterised types and was
  never updated. `Import DV.` and `Import …LP.Events.` fail; `L4`
  has the wrong kind for the existing `step` cofix.
- Multiple AST-extension commits (`samesign`, `splat`, `disjoint`,
  atomic ops, etc.) added new constructors that `ShowAST.v` never
  fully absorbed. The extracted `show prog` SEGVs at runtime on
  certain generated programs (confirmed by bisection: minimal property
  passes 1000 tests, the moment `show prog` is invoked we crash).

We **verified independently** in a fresh `git worktree add
/tmp/vellvm-dev-clean origin/dev` (zero NI changes) that vanilla
`origin/dev`'s `make qc-tests` reproduces the same `Cannot find
module DV` error. So the QC rot is upstream, not anything we did.

User asked: why not go back to the fork point where qc-tests was
working? Fair — that's what `ni-refactoring-stable` is. Same design,
ported to the old base where `QCVellvm.v` and `ShowAST.v` are still
internally consistent.

### Smoke tests (manual, both branches)

| Fixture | Behavior | TOBS_REGS | TOBS_ADDRS | Trace |
|---|---|---|---|---|
| `leak_test1_simple_branch.ll` (branch on `icmp sgt %secret, 50`) | secret=100 → ret 1; secret=0 → ret 0 | `cmp, secret` | (empty) | diverges at final `Br(true/false)` |
| `leak_test3_memory_only.ll` (load `arr[secret % 4]`) | secret=2 → ret 30 | `data_ptr, idx, secret, p0..p3, arr` | `282, 286, 290, 294` | diverges at load address |
| `leak_test5_no_leak.ll` (secret only in arithmetic) | any secret → ret `secret + 42` | `x` | `282` | **identical** for secrets 10 and 99 |

`leak_test5` is the key validation: `secret ∉ TOBS_REGS` and traces
match across secret values — exactly what the partition design
predicts.

### Automated QC (stable branch only)

```
make ni-tests
  → QuickChecking (forAll ... vellvm_taint_soundness_partition)
  → +++ Passed 1000 tests (0 discards)
  → Time Elapsed: 93.029875s
```

Property: for each random `Prog` with `main(i32 %secret)`, find
`secret`'s `raw_id`. Shell out for the partition; shell out twice for
two traces (secrets 42 and 137). If `secret ∉ TOBS_REGS`, the traces
must match — otherwise the tracker is unsound. 1000 iterations
produced no counterexample.

`make qc-tests` (the upstream `vellvm_agrees_with_clang` test) builds
and runs 766 iterations before hitting an interpreter-vs-clang
counterexample. That counterexample is a separate
interpreter-correctness issue, **not** related to the NI work.

---

## Final state on disk

```
/home/yonghyunkim/works/vellvm/   (WSL2, opam switch 'vellvm')

Branches:
  ni-refactoring-stable  c0bf7d01  ← current HEAD, daily driver
  ni-refactoring         35f58726  partition design on origin/dev
  ni-taint-semantic      da039a52  prior layer-1+layer-2 (preserved)
  dev                    9557f168  fork point (behind origin/dev by 131)
  origin/dev             f1ec3588  current upstream

Untracked (do NOT commit — your local env):
  .claude/                                     Claude CLI state
  .mcp.json                                    MCP config
  src/SpecIBT-old/                             your historical reference
  src/_qc_SpecIBT-old.tmp/                     scratch
  vellvm-old/                                  historical reference
```

### Key files in the refactor (identical between the two ni-refactoring* branches)

| File | What's there |
|---|---|
| `src/rocq/NI/TaintTracker.v` | The partition-style tracker (~440 LOC). `taint = list (raw_id + Z)`, `tstate`, `calc_taint_exp`, `taint_instr_pure`, `taint_phi_gen`, `taint_term_gen`, then `Module Make (LP : LLVMParams) (MEM : Memory LP)` with `denote_instr_taint` / `denote_code_taint` / `denote_block_taint` / `denote_ocfg_taint` / `denote_cfg_taint` / `denote_function_taint`. Concrete instantiations `TaintTracker64` + `TaintTrackerBigIntptr`. |
| `src/rocq/QC/NITests.v` | The `vellvm_taint_soundness_partition` QC property + shell-out axioms (`vellvm_collect_obs_args_str`, `vellvm_taint_public_reg_names_str`). |
| `src/rocq/Semantics/LLVMEvents.v` | `+ DebugBranch : bool -> DebugE unit` constructor + `debug_branch` helper. |
| `src/rocq/Semantics/Denotation.v` | `+ debug_branch true/false` emission in `TERM_Br`. |
| `src/rocq/Semantics/InterpretationStack.v` | `+ ZArith` import, `event_obs`, `observe_L2` (`CoFixpoint` with `Unset Guard Checking`), `interp_mcfg4_exec_obs`. |
| `src/rocq/Semantics/TopLevel.v` | `+ interpreter_gen_obs` (mirrors `interpreter_gen` but uses `interp_mcfg4_exec_obs`). |
| `src/rocq/Theory/DenotationTheory.v` | One extra `apply has_post_bind; intros [];` step in the `Br` case of `denote_term`'s proof, to consume the new `debug_branch ;;` bind. |
| `src/rocq/QC/GenAST.v` | + 5 generators: `gen_main_with_secret`, `gen_main_with_args`, `gen_llvm_with_args`, `gen_llvm_with_secret`, `gen_llvm_with_secret_nofun` (no helper functions — required by the taint tracker which doesn't recurse into `CallE`). |
| `src/ml/interpreter.ml` | `+ interpret_with_args_obs`, `interpret_with_args_taint_obs`, plus `step_obs` / `step_taint_obs` helpers walking the L4 itree. |
| `src/ml/driver.ml` | `+ interpret_obs_args` / `taint_track_args` refs, `parse_int_args`, `print_obs_trace`, `print_raw_id`, `print_tobs_partition`. |
| `src/ml/main.ml` | `+ 2` flag registrations. |
| `src/ml/extracted/Extract.v` | `+ NI.TaintTracker` to the `From Vellvm Require` list and the `Separate Extraction` line. |
| `src/fix-extraction.sh` | `+ TaintTracker.{ml,mli}` in `EXECPOSTFILES` (strips broken `exec_correct_post` declarations from the extracted .mli). |
| `src/Makefile` | `+ ni-tests` target (`VELLVM_BIN="$$(pwd)/vellvm" $(ROCQEXEC) rocq/QC/NITests.v`). |
| `src/_RocqProject` | `+ ./rocq/NI/TaintTracker.v`. 7 `InfiniteToFinite*.v` files commented out for build speed (they're heavyweight refinement proofs not needed for NI testing — only the `BigIntptr` model is used at runtime). |

> **Superseded (2026-06-02).** The 5 `GenAST.v` generators noted above
> (`gen_main_with_secret`, `gen_main_with_args`, `gen_llvm_with_args`,
> `gen_llvm_with_secret`, `gen_llvm_with_secret_nofun`) and the wrapper
> `gen_PROG_with_secret_nofun` were later **removed**. The NI test now uses
> `gen_llvm_with_args_nofun` (size-scaled i32 args, no helper functions) with
> a public-equivalent input-pair check. See
> [NI_ARCHITECTURE.md](NI_ARCHITECTURE.md).

### Files different between the two branches

The Rocq files have minor adaptations between branches because of
upstream drift. `ni-refactoring-stable` has:

- `calc_taint_exp` in `TaintTracker.v` includes cases for `EXP_Hex` /
  `EXP_Double` (which exist on the old base but not on dev),
  and no cases for `EXP_Splat` / `EXP_Asm` / `EXP_Metadata` / `OP_Fneg`.
- `OP_ICmp` matched with 4 args (no `samesign`).
- `INSTR_Call` matched with 3 args.
- `denote_instr_taint` takes `(instr_id * instr dtyp)` pair (no
  metadata triple); `blk_phis` / `blk_term` similar.
- `denote_function_taint` inlines the call-frame setup (no
  `push_call_frame` / `pop_call_frame` helpers at the fork point).
- L2/L4 not parameterised on `dvalue uvalue`.
- DebugE at position 7 in L2 → 6 `inr1`s + `inl1` (vs 7 on dev).
- L4 has 5 events on old base (no `LLVMExcE`).
- `Import LP.Events.` in `TaintTracker.v`'s `Make` module (the
  submodule still exists at the fork point).
- `rocq/QC/QCVellvm.v` has one new patch: a dependent inner match on
  `DebugE` so the existing `step` cofix can pass through the new
  `DebugBranch` constructor.
- `fix-extraction.sh` uses the OLD branch's version (with
  `.Events.DV` substitutions for the parameterised events).
- `Extract.v` keeps the `mathcomp.ssreflect.ssreflect` removal patch
  the user did in commit `c1e7e920`.

### Docs (both branches, content same modulo "QC harness blocked" caveat)

| Doc | What's in it |
|---|---|
| `src/NI_TESTING.md` | Per-flag CLI reference. Two flags only. Output markers + encodings. Worked examples on `ni_examples/` fixtures. Code pointers (file:line) for each flag's dispatch path. |
| `src/NI_ARCHITECTURE.md` | Framework architecture. The three-piece picture (generator / NI tester / tracker). Observation pipeline at L2. Self-tagging trick. `denote_instr_taint` Load/Store duplication explanation. |
| `src/REFACTORING_REPORT.md` | Phase-by-phase narrative of the refactor. Drift hits and resolutions. End-of-section codebase state summaries. (On the `dev`-based branch, also documents the upstream QC blocker; on the stable branch, the blocker section is moot — both targets work.) |

### Fixtures

`ni_examples/` contains 7 `.ll` programs:

- `leak_test1_simple_branch.ll` — branch leak only
- `leak_test2_nested_branch.ll` — nested branches, 4 paths
- `leak_test3_memory_only.ll` — memory-address leak via GEP
- `leak_test4_branch_and_memory.ll` — combined
- `leak_test5_no_leak.ll` — no leak
- `leak_test6_branch_diff_alloca.ll` — branch + per-side alloca
- `leak_test_two_args.ll` — multi-arg main for `-interpret-obs-args 5,3`

Plus `ni_examples/README.md` walking through each fixture.

---

## How to continue from a new machine

```bash
git clone https://github.com/vellvm/vellvm
cd vellvm
git fetch origin
git checkout ni-refactoring-stable    # daily driver, QC works

cd src
# need: opam switch with rocq + coq-quickchick installed
make
make qc-tests   # builds + runs upstream agreement test
make ni-tests   # builds + runs partition-style soundness test (1000 iters, ~93s)
```

If the new machine doesn't have the project's branches, push them
first:

```bash
git push <fork-remote> ni-refactoring-stable ni-refactoring ni-taint-semantic
```

The branches `ni-refactoring` and `ni-refactoring-stable` are both
single-commit refactors over their respective base. Each commit message
itemises everything in the commit (see `git log -1`).

---

## Open work / known limitations

### On `ni-refactoring` (dev-based branch)

The QC harness is **blocked upstream**, not by anything in the refactor.
Reviving `make qc-tests` / `make ni-tests` requires repairing two
files that upstream let rot after the `19206d18` module refactor:

1. **`rocq/QC/QCVellvm.v`** — propagate `dvalue uvalue` parameters
   through every `L0..L4` reference, drop the `Import DV.` and
   `Import …LP.Events.` lines, fix the `single_step` matcher for the
   added `LLVMExcE uvalue` event.
2. **`rocq/QC/ShowAST.v`** — audit every constructor in today's
   `exp` / `instr` / `terminator` and ensure each has a Show case;
   round-trip-test against the parser. The crash is here: extracted
   `show prog` SEGVs at runtime on certain generated programs.

`NITests.v` is **already self-contained** and will run unchanged once
those are repaired — no NI-side changes needed.

### On `ni-refactoring-stable` (fork-point branch)

Everything works today. The trade-off is it doesn't include 131
upstream commits, which include:

- The Infinite ↔ Finite refinement proofs (excluded anyway for build
  speed).
- Debugger + fast-execution mode (`ba634a3d`).
- Atomic instructions, fence, cmpxchg, atomicrmw.
- Metadata threading via `(_, _, list metadata)` triples.
- The `Llvm_printer` extraction improvements (we don't rely on those).
- The `Ceres` removal (we don't rely on Ceres).

If/when upstream's `QCVellvm.v` + `ShowAST.v` are repaired, the
refactor can be replayed on top of dev with the existing
`ni-refactoring` branch as the starting point.

### Cumulative blind spots in the tracker (both branches)

Today's `gen_PROG_with_secret_nofun` produces a subset of LLVM that
the tracker fully models. If the generator is extended to include any
of these instruction kinds, the tracker will silently default to "no
flow" (unsound):

- `INSTR_Atomicrmw` / `INSTR_Cmpxchg` / `INSTR_Fence`
- `TERM_Invoke` / `TERM_Resume`
- `EXP_Asm`

Adding cases to `taint_instr_pure` / `taint_term_gen` / `calc_taint_exp`
in `TaintTracker.v` is mechanical (~10 lines per construct).

---

## Things to know about the user's environment

- **Native Ubuntu Linux** (as of 2026-05-19). Earlier sessions were on
  WSL2 on Windows — historical notes in this doc may still reference
  WSL behavior. One stack-overflow-style crash on the old WSL setup
  turned out to be unrelated to WSL anyway (`ulimit -s unlimited`
  didn't help); on native Linux there's no reason to suspect
  WSL-specific issues.
- Opam switch name: `vellvm`.
- The user has `~/works/vellvm/SpecIBT-old/` as a reference (the
  earlier project they wrote that inspired the partition design).
  Don't confuse it with the active code.
- `.claude/` and `.mcp.json` at the repo root are local agent state —
  do NOT commit.
- `vellvm-old/` and `src/SpecIBT-old/` are historical references — do
  NOT commit.

---

## Design rationale / FAQ

**Why partition design instead of "designated sources"?** Cleaner
semantics. The complement of `TOBS_REGS` is a *guarantee* (those
variables don't leak), not just "the tracker hasn't been asked about
them." The harness can pick any variable from the complement and
soundly vary it.

**Why is the shellout in the QC test so verbose?** Coq's extraction
generates non-unifying `itree L0` OCaml types across different
`LP`/`MEM` instantiations of the pipeline. Calling the pipeline
directly from QC's compile context produces type errors. The
shellout (write program to temp file, run `./vellvm`, parse framed
markers) is the cleanest workaround.

**Why is `gen_*_nofun` the only generator used in QC?** The taint
tracker's `denote_function_taint` doesn't recurse into `CallE`
events — `interp_mrec` is given a trivial handler that returns
`Obj.magic ()`. If the generated program calls a helper, the result
is garbage. The `_nofun` generator skips
`gen_helper_function_tle_multiple`.

**Why is `_CoqProject` a symlink?** It's `_RocqProject` on disk —
`_CoqProject` is `lrwxrwxrwx → _RocqProject`. The repo uses both names
for historical compatibility.

**Why exclude `InfiniteToFinite/*.v` in `_RocqProject`?** They're
heavyweight refinement proofs between the Infinite and BigIntptr
memory models. NI testing only uses `BigIntptr` (the runtime
interpreter), so these proofs are pure compile-time cost. The
exclusion in `_RocqProject` shaves a lot off `make`.

**Why does `make` rebuild ~20 downstream files even after a clean
build completes?** That's a pre-existing project quirk — the STAMP
rule in `src/Makefile` both *depends on* `$(EXEC_VOFILES)` and
*re-invokes* `make $(EXEC_VOFILES)` in its body, which causes some
EXEC files to be rebuilt with newer mtimes than their consumers. The
next `make` invocation then rebuilds the consumers. Settles in two
passes. Removing the redundant `make $(EXEC_VOFILES)` in the recipe
would fix it. Not done; harmless.

---

## File-by-file walkthrough of the key Rocq design

If you need to dive in:

1. **Read `src/rocq/NI/TaintTracker.v` top to bottom.** It's
   self-contained and well-commented. Sections in order:
   - Source identities (`taint_src`, `taint`, `join_taints`).
   - Lookup maps with self-tagging defaults (`treg_lookup`,
     `tmem_lookup`).
   - `tstate` record + `split_taint` for partition output.
   - `Section ExpTaint` — pure expression taint (`calc_taint_exp`).
   - `Section PureUpdates` — `taint_instr_pure`, `taint_phi_gen`,
     `taint_term_gen` (AST-only).
   - `Module Make (LP : LLVMParams) (MEM : Memory LP)` — the
     semantic Load/Store handling, `denote_instr_taint` etc.

2. **Read `src/rocq/Semantics/InterpretationStack.v`** for the
   instrumentation: `event_obs` (which events get serialised) and
   `observe_L2` (the cofixpoint that walks an L2 itree, accumulates
   the obs list, re-emits events unchanged).

3. **Read `src/rocq/QC/NITests.v`** for the harness: shows the
   shell-out pattern and the soundness property.

That's the whole conceptual core. Everything else is plumbing.

---

## End of handover

Last working state (as of this handover):

```
$ cd src && make ni-tests
…
+++ Passed 1000 tests (0 discards)
Time Elapsed: 93.029875s
```

If the new thread / next session finds something broken on first
build, the first sanity check is:

```bash
ls ml/extracted/*.ml | wc -l        # should be ~100, no .ml leftover from other branch
rm -f ml/extracted/STAMP             # force re-extract
make                                 # full clean build
```

The most common pitfall when switching branches is stale `.ml` files
in `ml/extracted/` from a previous branch's extraction — those
reference modules that may not exist on the new branch.
