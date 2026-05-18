# NI (Non-Interference) Test Examples

Test programs for verifying the observation-based NI checker in Vellvm. Each program takes `i32 %secret` as an argument to `main`. The checker compares observation traces from two runs with different secrets — if the traces differ, it's an NI violation.

## How to Run

```bash
cd src
./vellvm -interpret-obs-args <secret_value> ../ni_examples/<file>.ll
./vellvm -taint-track-args  <secret_value> ../ni_examples/<file>.ll
```

The flag takes a **comma-separated list of i32 args**; for the
single-secret fixtures here, just pass one integer. For
[leak_test_two_args.ll](leak_test_two_args.ll) use e.g.
`-interpret-obs-args 5,3`.

### Observation trace (`OBS_TRACE`)

Both flags emit the trace between `---OBS_TRACE_BEGIN---` and
`---OBS_TRACE_END---`:

- Negative number = `OStore(addr)` — store to memory address
- Positive number (< 1000000) = `OLoad(addr)` — load from memory address
- `1000000` = `OBranch(true)` — conditional branch took the true path
- `1000001` = `OBranch(false)` — conditional branch took the false path

### Partition output (`-taint-track-args` only)

`-taint-track-args` additionally emits the **public partition** —
SSA register names and memory addresses that influenced an observation
event during this run:

- `---TOBS_REGS_BEGIN---` … `---TOBS_REGS_END---`: register names
- `---TOBS_ADDRS_BEGIN---` … `---TOBS_ADDRS_END---`: memory addresses

Any source identity **not** in either list is safe to vary across
runs without changing the observation trace. For NI, the question is
whether `secret` (the SSA name of `main`'s i32 parameter) appears in
`TOBS_REGS`:

- `secret ∈ TOBS_REGS` → the program leaks `secret` through observations.
- `secret ∉ TOBS_REGS` → varying `secret` is safe; traces must match.

See [src/NI_TESTING.md](../src/NI_TESTING.md) for the full CLI reference
and [src/NI_ARCHITECTURE.md](../src/NI_ARCHITECTURE.md) for the
framework design.

## Test Files

### 1. `leak_test1_simple_branch.ll` — Branch leakage only

A single secret-dependent conditional branch. No secret-dependent memory access.

```bash
./vellvm -interpret-obs-args 100 ../ni_examples/leak_test1_simple_branch.ll
# Trace: ...S(298), Br(true)

./vellvm -interpret-obs-args 0 ../ni_examples/leak_test1_simple_branch.ll
# Trace: ...S(298), Br(false)
```

**Expected**: Traces differ at the branch observation. NI violation via branch leakage.

---

### 2. `leak_test2_nested_branch.ll` — Multiple nested branches

Two levels of secret-dependent branches, producing 4 distinct execution paths.

```bash
./vellvm -interpret-obs-args 90 ../ni_examples/leak_test2_nested_branch.ll   # Br(T), Br(T) → ret 3
./vellvm -interpret-obs-args 60 ../ni_examples/leak_test2_nested_branch.ll   # Br(T), Br(F) → ret 2
./vellvm -interpret-obs-args 30 ../ni_examples/leak_test2_nested_branch.ll   # Br(F), Br(T) → ret 1
./vellvm -interpret-obs-args 10 ../ni_examples/leak_test2_nested_branch.ll   # Br(F), Br(F) → ret 0
```

**Expected**: All 4 paths produce distinct branch observation sequences.

---

### 3. `leak_test3_memory_only.ll` — Memory leakage only

Secret-dependent array index via `getelementptr` with a variable index (`srem %secret, 4`). No conditional branches in the program.

```bash
./vellvm -interpret-obs-args 0 ../ni_examples/leak_test3_memory_only.ll
# Trace: ...S(298), S(302), S(306), S(310), L(298)   ← loads arr[0]

./vellvm -interpret-obs-args 2 ../ni_examples/leak_test3_memory_only.ll
# Trace: ...S(298), S(302), S(306), S(310), L(306)   ← loads arr[2]
```

**Expected**: Traces differ at the final load address. NI violation via memory access pattern.

---

### 4. `leak_test4_branch_and_memory.ll` — Both branch AND memory leakage

Secret-dependent branch where each path loads from a different array element. Both leakage channels are visible in the trace.

```bash
./vellvm -interpret-obs-args 100 ../ni_examples/leak_test4_branch_and_memory.ll
# Trace: ...S(298), S(302), Br(true), L(298)    ← true branch, loads arr[0]

./vellvm -interpret-obs-args 0 ../ni_examples/leak_test4_branch_and_memory.ll
# Trace: ...S(298), S(302), Br(false), L(302)   ← false branch, loads arr[1]
```

**Expected**: Traces differ at both the branch observation AND the load address. Branch and memory observations appear in chronological order.

---

### 5. `leak_test5_no_leak.ll` — No leakage (negative test)

Secret is used only in arithmetic (`add %secret, 42`), never in a branch condition or memory address. The memory access pattern is identical regardless of the secret.

```bash
./vellvm -interpret-obs-args 42 ../ni_examples/leak_test5_no_leak.ll
# Trace: ...S(298), S(298), L(298)

./vellvm -interpret-obs-args 99 ../ni_examples/leak_test5_no_leak.ll
# Trace: ...S(298), S(298), L(298)
```

**Expected**: Traces are identical. No NI violation — the secret does not influence observable behavior.

---

### 6. `leak_test6_branch_diff_alloca.ll` — Branch with different allocation patterns

Secret-dependent branch where one path does 1 alloca + 1 store + 1 load, and the other does 2 allocas + 2 stores + 2 loads. The traces differ in both branch direction and length.

```bash
./vellvm -interpret-obs-args 5 ../ni_examples/leak_test6_branch_diff_alloca.ll
# Trace: ...Br(true), S(298), L(298)                     ← 1 alloca path

./vellvm -interpret-obs-args -5 ../ni_examples/leak_test6_branch_diff_alloca.ll
# Trace: ...Br(false), S(298), S(302), L(298), L(302)    ← 2 alloca path
```

**Expected**: Traces differ in branch observation, number of store/load events, AND trace length. This is the most comprehensive leakage pattern — an attacker can distinguish runs by any of these differences.

---

## Summary Table

| Test | Branch leak | Memory leak | Trace length differs | NI violated? |
|---|---|---|---|---|
| 1. Simple branch | Yes | No | No | Yes |
| 2. Nested branch | Yes (multiple) | No | No | Yes |
| 3. Memory only | No | Yes (load addr) | No | Yes |
| 4. Branch + memory | Yes | Yes (load addr) | No | Yes |
| 5. No leak | No | No | No | **No** |
| 6. Branch + diff alloca | Yes | Yes (different ops) | Yes | Yes |

## Observation Model

The observation trace records three types of events:

| Observation | Source | What it captures |
|---|---|---|
| `OStore(addr)` | `Store` instruction at L2 | Which memory address is written to |
| `OLoad(addr)` | `Load` instruction at L2 | Which memory address is read from |
| `OBranch(bool)` | `br i1` (conditional branch) in denotation | Which direction the branch took |

All observations are recorded in **chronological order** — the trace reflects the exact sequence of memory accesses and branch decisions during execution.
