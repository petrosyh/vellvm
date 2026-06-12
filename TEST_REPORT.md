# NI Test Report

Running log of non-interference (NI) test campaigns for the Vellvm taint
tracker. One entry per campaign: commit under test, date, what was tested,
results, and the key statistics. Newest entries at the top.

Property under test (unless stated otherwise): *NI soundness* — for a
randomly generated multi-arg program, the taint tracker's public partition
must be safe: varying any argument outside the partition must not change
the observation trace (Load/Store addresses, branch directions, call
targets). A counterexample means the tracker under-tainted.

**Reproduction** (any entry): check out the commit, then

```
cd src
make vellvm && make rocq/NI/TaintTracker.vo rocq/QC/GenAST.vo \
               rocq/QC/ShowAST.vo rocq/QC/ReprAST.vo
./run_ni_parallel.sh <workers> <tests-per-worker> <timeout-s> <outdir> 5
```

with the worker/test counts from the entry's setup line. Entries that
test an *uncommitted* patch say so explicitly and name the file where
the patch is preserved. Program-corpus statistics additionally use the
optional wrapper `src/ni_corpus_wrapper.sh` (instructions in its
header) and `src/ni_corpus_stats.py` — neither affects test results.

---

## 2026-06-12 — erasure check: obs instrumentation is conservative

- **Commit**: `f4f027a3` (semantics code identical to `c0c0bd6a`).
- **Property**: erasing the observation instrumentation must leave the
  original Vellvm semantics. For each program: path A = our
  `-interpret-obs-args` pipeline on the original program; path B = the
  stock `-interpret` pipeline (no observation tap) on a wrapper that
  bakes the same arguments in as constants. Compared: termination class
  and final dvalue / error reason (obs output deliberately ignored).
- **Scope caveat**: both paths share this fork's *denotation*, which
  already emits the added branch/call debug events (Denotation.v). This
  campaign therefore validates the `observe_L2` tap and the argument
  injection, but NOT the debug-event extension itself (common to both
  paths). Validating that last delta needs a true-upstream baseline
  build — tracked as follow-up work.
- **Setup**: replay of the full 8,484-program corpus, deterministic
  per-file argument vectors, 12-way parallel, 5 s timeout.
- **Result**: **0 real divergences.** 8,401 identical results, 80
  identical error reasons, 1 double-timeout (neutral). 2 one-sided
  timeouts re-run in isolation: both match — parallel-load flakes.
- **Tools**: `src/erasure_corpus_check.sh` (corpus replay);
  `src/rocq/QC/ErasureTests.v` + `src/run_erasure_parallel.sh`
  (generative variant of the same property, for ongoing campaigns).

## 2026-06-12 — generated-program corpus statistics

- **Commit**: `c0c0bd6a` (generator identical in all campaigns above).
- **Setup**: every program shelled out during an 8 × 1,000 campaign
  (2 s timeout) was archived via `ni_corpus_wrapper.sh` →
  **8,484 unique programs** (passes and discards; count matches the
  8,503 attempts).
- **Statistics**:
  - Lines: avg **270**, median 182, p90 648, max **1,781**.
  - Instructions: avg 118, median 89, max 553. Functions: avg 3.5,
    max 8. Basic blocks: avg 13, max 61.
  - **63.0% of programs contain loops** (back-edge heuristic).
  - Instruction mix: memory/pointer-heavy — store 15.1%, load /
    getelementptr / alloca / bitcast / ptrtoint ≈7.5% each (≈45%
    combined), call 5.4%, br 5.8%, icmp 4.1%.
- **Note**: QuickChick's size parameter ramps across each campaign, so
  this distribution is representative of the other campaigns with this
  generator (including the 100k run, whose program texts were not
  retained).

## 2026-06-11/12 — 100k overnight soundness run

- **Commit**: `c0c0bd6a` (inter-procedural taint, address-based call
  resolution, call-target obs)
- **Setup**: 8 parallel workers × 12,500 tests, 2 s shell-out timeout,
  independent RNG seeds per worker.
- **Result**: **100,000 / 100,000 passed, 0 failures.**
- **Statistics**:
  - 108,596 generation attempts; 8,596 discards (7.92%):
    5,995 partner-identical (5.52%), 2,499 baseline UB/error (2.30%),
    102 timeout (0.094%).
  - Per-worker discards 999–1,155 (max/min 1.16×) — distributions
    consistent across the 8 independent seeds.
  - Wall time ~12.1 h; throughput 137.5 passed tests/min (≈3.5 s per
    test per worker); ~209k interpreter executions total.
  - Runtime is not linear in test count: QuickChick's size parameter
    ramps over the whole run, so larger campaigns spend more time per
    test on average (an 8×1,000 run sustains ~258 tests/min).

## 2026-06-11 — 8k quick validation run

- **Commit**: `c0c0bd6a`
- **Setup**: 8 workers × 1,000 tests; first run with shell-out timeout
  reduced 5 s → 2 s.
- **Result**: **8,000 / 8,000 passed, 0 failures.**
- **Statistics**:
  - 544 discards (~6.4% of attempts): 414 partner-identical,
    128 baseline UB/error, 2 timeout.
  - Wall time ~31 min (~258 passed tests/min).
  - Timeout discards at 2 s were negligible (2 of 8,544 attempts),
    validating the faster setting used by all subsequent campaigns.
