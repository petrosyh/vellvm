# NI Testing — CLI Flag Reference

Per-flag guide for testing single `.ll` files with the partition-style NI
framework. Run from `src/` after `make`.

```bash
./vellvm <flag> <args> <file.ll>
```

Two flags do all the work:

| Flag | Purpose |
|---|---|
| `-interpret-obs-args <n1,n2,…>` | Run the program with i32 args; emit the observation trace. |
| `-taint-track-args <n1,n2,…>` | Run the partition-style taint tracker; emit both the public partition and the observation trace. |

Sample programs live in [../ni_examples/](../ni_examples/) — each
defines `define i32 @main(i32 %secret)` (or `main(i32 %a, i32 %b)` for
the multi-arg fixture).

For the architecture behind these flags see
[NI_ARCHITECTURE.md](NI_ARCHITECTURE.md).

## Output markers and encodings

| Marker pair | Contents |
|---|---|
| `---OBS_TRACE_BEGIN---` / `---OBS_TRACE_END---` | One integer per line; encoded observation events |
| `---TOBS_REGS_BEGIN---` / `---TOBS_REGS_END---` | SSA register names in the public partition |
| `---TOBS_ADDRS_BEGIN---` / `---TOBS_ADDRS_END---` | Memory addresses in the public partition |

**Observation event encoding** (see `event_obs` in
[rocq/Semantics/InterpretationStack.v](rocq/Semantics/InterpretationStack.v)):

| Value | Meaning |
|---|---|
| `n > 0`, `n < 1000000` | `OLoad(addr=n)` |
| `n < 0` | `OStore(addr=-n)` |
| `1000000` | `OBranch(true)` |
| `1000001` | `OBranch(false)` |

**Variable name format** in `TOBS_REGS`:

| Coq side | Printed form |
|---|---|
| `Name "x"` | `x` |
| `Anon n` | `anon_n` |
| `Raw n` | `raw_n` |

## Partition-style semantics in one sentence

`TOBS_REGS` and `TOBS_ADDRS` together are the **public partition** —
the set of source identities (SSA names and memory cells) whose values
influenced an observation event during this run. **Anything not in those
two lists can be varied across runs without changing the observation
trace.**

---

## `-interpret-obs-args <n1,n2,…>`

**Purpose.** Run the interpreter with a comma-separated list of `i32`
arguments fed to `main`, and emit the L2 observation trace
(`observe_L2` over `interp_mcfg4_exec_obs`).

**Usage.**
```bash
./vellvm -interpret-obs-args <int>[,<int>,…] <file.ll>
```

**Output.**
```
Program terminated with: <dvalue>
---OBS_TRACE_BEGIN---
<int>
<int>
…
---OBS_TRACE_END---
```

**Example — same program, two secrets.**
```bash
./vellvm -interpret-obs-args 100 ../ni_examples/leak_test1_simple_branch.ll
./vellvm -interpret-obs-args 0   ../ni_examples/leak_test1_simple_branch.ll
```

For [leak_test1](../ni_examples/leak_test1_simple_branch.ll)
(`%cmp = icmp sgt i32 %secret, 50; br i1 %cmp, …`):

```
secret=100:  Program terminated with: i32 1
             Trace:  … -282  1000000        (Br true)

secret=0:    Program terminated with: i32 0
             Trace:  … -282  1000001        (Br false)
```

Identical store prefix, divergence at the final event → branch leak.

**Example — multi-arg `main`.** With
[leak_test_two_args.ll](../ni_examples/leak_test_two_args.ll)
(`main(i32 %a, i32 %b)`, branch on `icmp sgt %a %b`):

```bash
./vellvm -interpret-obs-args 5,3 ../ni_examples/leak_test_two_args.ll   # → Br(true), ret 1
./vellvm -interpret-obs-args 3,5 ../ni_examples/leak_test_two_args.ll   # → Br(false), ret 0
```

**Code pointers.**

- OCaml dispatch: [src/ml/driver.ml](src/ml/driver.ml) (`-interpret-obs-args` branch in `process_ll_file`)
- OCaml entry: [src/ml/interpreter.ml](src/ml/interpreter.ml) (`interpret_with_args_obs`)
- Rocq top-level: [rocq/Semantics/TopLevel.v](rocq/Semantics/TopLevel.v) (`interpreter_gen_obs`)
- Rocq pipeline: [rocq/Semantics/InterpretationStack.v](rocq/Semantics/InterpretationStack.v) (`interp_mcfg4_exec_obs`)
- Trace recorder: same file, `observe_L2` (cofixpoint)
- Event extraction: same file, `event_obs`

---

## `-taint-track-args <n1,n2,…>`

**Purpose.** Run the partition-style taint tracker against the program
with the supplied i32 args. Output the public partition (register
names and memory addresses that flowed into an observation event) and
the observation trace.

In the partition design every SSA variable is `inl id` and every memory
cell is `inr addr`, and they self-tag automatically — there are no
caller-supplied "secret" inputs. The harness decides what to vary by
inspecting the partition.

**Usage.**
```bash
./vellvm -taint-track-args <int>[,<int>,…] <file.ll>
```

**Output.**
```
Program terminated with: <dvalue>
---TOBS_REGS_BEGIN---
<varname>
…
---TOBS_REGS_END---
---TOBS_ADDRS_BEGIN---
<addr>
…
---TOBS_ADDRS_END---
---OBS_TRACE_BEGIN---
<int>
…
---OBS_TRACE_END---
```

**Example — branch leak.**
```bash
./vellvm -taint-track-args 7 ../ni_examples/leak_test1_simple_branch.ll
```
```
Program terminated with: i32 0
---TOBS_REGS_BEGIN---
cmp
secret
---TOBS_REGS_END---
---TOBS_ADDRS_BEGIN---
---TOBS_ADDRS_END---
---OBS_TRACE_BEGIN---
… 1000001
---OBS_TRACE_END---
```
`secret` is in `TOBS_REGS` → the program is allowed to behave
differently across secrets. `TOBS_ADDRS` is empty because no Load/Store
revealed a secret-dependent address.

**Example — memory leak.**
```bash
./vellvm -taint-track-args 2 ../ni_examples/leak_test3_memory_only.ll
```
```
---TOBS_REGS_BEGIN---
data_ptr  idx  secret  p3  p2  p1  p0  arr
---TOBS_REGS_END---
---TOBS_ADDRS_BEGIN---
294  290  286  282
---TOBS_ADDRS_END---
```
The full data-flow chain into the load address shows up in
`TOBS_REGS`, and every memory cell touched by Store/Load is listed in
`TOBS_ADDRS`.

**Example — no leak.**
```bash
./vellvm -taint-track-args 100 ../ni_examples/leak_test5_no_leak.ll
```
```
---TOBS_REGS_BEGIN---
x
---TOBS_REGS_END---
---TOBS_ADDRS_BEGIN---
282
---TOBS_ADDRS_END---
```
`secret` is **not** in `TOBS_REGS` → varying `secret` is safe; running
this program with any two i32 values produces identical observation
traces. (Confirmed: traces for secret=10 and secret=99 are bitwise
identical.)

**Code pointers.**

- OCaml dispatch: [src/ml/driver.ml](src/ml/driver.ml) (`-taint-track-args` branch + `print_tobs_partition`)
- OCaml entry: [src/ml/interpreter.ml](src/ml/interpreter.ml) (`interpret_with_args_taint_obs`)
- Rocq module: [rocq/NI/TaintTracker.v](rocq/NI/TaintTracker.v)
  (`Module Make`, `TaintTrackerBigIntptr`)
- Key Rocq definitions:
  - `taint = list (raw_id + Z)` — the alphabet of source identities
  - `treg_lookup` and `tmem_lookup` — self-tag on every read (the trick that turns "every variable / cell is its own source" from an init-time concern into an O(1) lookup)
  - `denote_function_taint` — entry point; threads `tstate` through the interpretation
  - `denote_instr_taint` — duplicates Load/Store for concrete addresses; delegates other ops to `denote_instr`

---

## Composing flags

The two flags are independent and can run side-by-side on a single
invocation. Each emits its own framed sections in the order printed
above.

```bash
./vellvm -interpret-obs-args 7 -taint-track-args 7 leak_test4.ll
```

Useful for cross-checking that the trace is identical between the
plain-interpret pass and the taint-augmented pass — they share the
exact same observation pipeline, so they should always agree.

---

## QC integration (status)

A QuickChick property `vellvm_taint_soundness_partition` is defined
in [rocq/QC/NITests.v](rocq/QC/NITests.v) and exposed via
`make ni-tests`. It samples random programs via
`gen_PROG_with_secret_nofun`, queries the tracker for the public
partition, picks a secret name from the complement, and asserts that
the observation traces under two different secret values agree.

As of this writing the automated invocation is **blocked on an
upstream regression**: `QCVellvm.v` on `origin/dev` no longer compiles
(`Cannot find module DV`, `L4` parameterisation drift). Vanilla
`make qc-tests` reproduces the same error in a fresh `origin/dev`
checkout. Once upstream's `QCVellvm.v` is updated, `make ni-tests`
will run the property unchanged. In the meantime the same soundness
check can be exercised by hand against the fixtures in
[../ni_examples/](../ni_examples/).
