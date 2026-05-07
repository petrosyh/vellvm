# NI Testing — CLI Flag Reference

Per-flag guide for testing single `.ll` files with the NI (non-interference) flags
added to the `vellvm` CLI. Run from `src/` after `make`.

```bash
./vellvm <flag> <args> <file.ll>
```

Sample programs live in [../ni_examples/](../ni_examples/) — each defines
`define i32 @main(i32 %secret)` so the secret-passing flags work directly.
For broader walkthroughs of the example programs see
[../ni_examples/README.md](../ni_examples/README.md).

## Common output markers

The flags emit framed sections on stdout so callers (e.g. the QC harness) can
extract them with simple line scanners:

| Marker pair | Contents |
|---|---|
| `---OBS_TRACE_BEGIN---` / `---OBS_TRACE_END---` | One integer per line; encoded observation events |
| `---TAINT_BEGIN---` / `---TAINT_END---` | One **source** variable name per line — inputs (e.g. `secret`) whose value influenced an observation (Layer 1 / pure AST) |
| `---TOBS_BEGIN---` / `---TOBS_END---` | Same shape as `TAINT_…` but from the Layer 2 / semantic tracker |

Observation event encoding (see `event_obs` in
[rocq/Semantics/InterpretationStack.v](rocq/Semantics/InterpretationStack.v)):

| Value | Meaning |
|---|---|
| `n > 0`, `n < 1000000` | `OLoad(addr=n)` |
| `n < 0` | `OStore(addr=-n)` |
| `1000000` | `OBranch(true)` |
| `1000001` | `OBranch(false)` |

Variable names: `Name "x"` prints as `x`, `Anon n` as `anon_n`, `Raw n` as `raw_n`.

---

## `-interpret-obs`

**Purpose.** Run the interpreter without passing a secret. Kept for backward
compatibility — does **not** emit an observation trace on its own (the original
ad-hoc `Obs_trace` module was never landed on this branch). Use
`-interpret-obs-secret` or `-interpret-obs-args` for an actual trace.

**Usage.**
```bash
./vellvm -interpret-obs <file.ll>
```

**Output.** Same as `-interpret`: a single line `Program terminated with: <dvalue>`
or `Program error: <reason>`. No `OBS_TRACE` markers.

**Example.**
```bash
./vellvm -interpret-obs ../ni_examples/leak_test5_no_leak.ll
# Note: leak_test5 expects an i32 arg; without -interpret-obs-secret/-args
# it runs with no secret. Use a no-arg program if you just want -interpret-obs.
```

---

## `-interpret-obs-secret <n>`

**Purpose.** Interpret with a single `i32 %secret = n` argument and emit the
Rocq-native L2 observation trace via `observe_L2` /
`interp_mcfg4_exec_obs`.

**Usage.**
```bash
./vellvm -interpret-obs-secret <secret_int> <file.ll>
```

**Output.**
```
Program terminated with: <dvalue>
---OBS_TRACE_BEGIN---
<int>
<int>
...
---OBS_TRACE_END---
```

**Example.**
```bash
./vellvm -interpret-obs-secret 100 ../ni_examples/leak_test1_simple_branch.ll
./vellvm -interpret-obs-secret 0   ../ni_examples/leak_test1_simple_branch.ll
```

**Expected.** For [leak_test1](../ni_examples/leak_test1_simple_branch.ll)
(`%cmp = icmp sgt i32 %secret, 50; br i1 %cmp, ...`), the two runs above
end with different branch markers (`1000000` vs `1000001`) — that diff is the
NI violation. For an example with diverging memory addresses see
[leak_test3_memory_only.ll](../ni_examples/leak_test3_memory_only.ll).

---

## `-interpret-obs-args <s>`

**Purpose.** Like `-interpret-obs-secret` but accepts a comma-separated list
of `i32` arguments — used when `main` takes multiple arguments. Pipeline:
`interpret_with_args_obs`.

**Usage.**
```bash
./vellvm -interpret-obs-args <n1>,<n2>,... <file.ll>
```

**Output.** Identical framing to `-interpret-obs-secret`:
```
Program terminated with: <dvalue>
---OBS_TRACE_BEGIN---
<int>
...
---OBS_TRACE_END---
```

**Example.** Using
[leak_test_two_args.ll](../ni_examples/leak_test_two_args.ll), whose `main`
branches on `icmp sgt i32 %a, %b`:

```bash
./vellvm -interpret-obs-args 5,3 ../ni_examples/leak_test_two_args.ll
./vellvm -interpret-obs-args 3,5 ../ni_examples/leak_test_two_args.ll
```

**Expected.**

For `5,3` (a > b → branch true → ret 1):
```
Program terminated with: i32 1
---OBS_TRACE_BEGIN---
-200
-280
-284
-289
-294
-298
1000000
---OBS_TRACE_END---
```

For `3,5` (a < b → branch false → ret 0): identical store prefix, then
`1000001` (`OBranch(false)`) instead of `1000000`. The diff at the final
event is the leak signal.

---

## `-taint-track`

**Purpose.** Layer 1 (pure AST) taint analysis — runs `Interpreter.taint_analyze`
over the program's AST without executing it. Reports which variable names the
analysis judges leaked. Conservative; ignores memory addresses.

**Usage.**
```bash
./vellvm -taint-track <file.ll>
```

**Output.**
```
---TAINT_BEGIN---
<varname>
<varname>
...
---TAINT_END---
```

`<varname>` is the LLVM identifier (e.g. `cmp`, `x`, `anon_3`).

**Example.**
```bash
./vellvm -taint-track ../ni_examples/leak_test1_simple_branch.ll
```

**Expected.** For [leak_test1](../ni_examples/leak_test1_simple_branch.ll),
the output is the single line `secret` between the markers — the branch
condition (`icmp sgt i32 %secret, 50`) carries `secret`'s taint, so `secret`
is reported as the leaked source. The analysis reports the **input** that
leaked, not the intermediate value (`%cmp`) it flowed through.

For [leak_test3](../ni_examples/leak_test3_memory_only.ll) (memory-only leak)
the output is also `secret`, since the GEP index `srem i32 %secret, 4`
carries the taint into a load address.

---

## `-taint-track-semantic <n>`

**Purpose.** Layer 2 / Option B — semantic taint tracking with memory
taint. Runs the program with `i32 %secret = n` through the
`SemanticTaintBigIntptr.denote_function_taint` pipeline and reports both the
leaked-variable set (`tobs`) and the observation trace.

**Usage.**
```bash
./vellvm -taint-track-semantic <secret_int> <file.ll>
```

**Output.**
```
Program terminated with: <dvalue>
---TOBS_BEGIN---
<varname>
...
---TOBS_END---
---OBS_TRACE_BEGIN---
<int>
...
---OBS_TRACE_END---
```

**Example.**
```bash
./vellvm -taint-track-semantic 7 ../ni_examples/leak_test4_branch_and_memory.ll
```

**Expected.**

For [leak_test4](../ni_examples/leak_test4_branch_and_memory.ll) (branch + memory leak):
```
Program terminated with: i32 200
---TOBS_BEGIN---
secret
---TOBS_END---
---OBS_TRACE_BEGIN---
-200
-280
-284
-289
-294
-298
-298
-302
1000001
302
---OBS_TRACE_END---
```

`TOBS` lists `secret` (the input that leaked); `OBS_TRACE` shows a `1000001`
(`OBranch(false)`) followed by a `OLoad(302)` — both are secret-dependent
events that will diverge against a different secret value.

For [leak_test5](../ni_examples/leak_test5_no_leak.ll) (no leak), `TOBS` is
empty (the markers print with nothing between them), and the trace contains
no branch markers and no secret-dependent addresses, so two runs with
different secrets produce identical traces.

> ⚠ Programs must not call helper functions — the semantic taint pipeline
> uses `denote_function_taint` and does not yet handle inter-procedural calls.
> Use the `gen_PROG_with_secret_nofun` generator when producing inputs from QC.

---

## Composing flags

The flags are independent and can be combined on a single invocation; each emits
its own framed sections. For example:

```bash
./vellvm -taint-track -taint-track-semantic 42 ../ni_examples/leak_test4_branch_and_memory.ll
```

prints `TAINT_…` (Layer 1), then `TOBS_…` (Layer 2), then `OBS_TRACE_…`.

Useful for cross-checking Layer 1 vs Layer 2 verdicts on the same input.
