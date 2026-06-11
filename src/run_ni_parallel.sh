#!/usr/bin/env bash
#
# Run the NI soundness QuickChick test (NITests.v) in parallel across N
# independent processes and aggregate the results.
#
# Each process seeds its RNG with Random.State.make_self_init () (reads system
# entropy), so the N processes explore *different* random programs -- no seed
# coordination needed. The test count per process and the per-shell-out timeout
# are set in NITests.v before launching (all processes share that file).
#
# Usage:  ./run_ni_parallel.sh [NPROC] [PER] [TIMEOUT] [OUTDIR] [STAGGER]
#   NPROC    number of parallel processes        (default 10)
#   PER      tests (defNumTests) per process      (default 10000)
#   TIMEOUT  per-shell-out timeout, seconds       (default 5)
#   OUTDIR   directory for per-process logs        (default /tmp/ni_parallel)
#   STAGGER  seconds to wait between launches      (default 5; smooths the
#            startup compile so N OCaml builds don't all spike memory at once)
#
# Total tests run ~= NPROC * PER. Failures stop their own process and dump the
# counterexample .ll (between <<<LLBEGIN ... LLEND>>>) into that process's log.
#
set -u
cd "$(dirname "$0")"                      # the src/ directory

NPROC="${1:-10}"
PER="${2:-10000}"
TIMEOUT="${3:-5}"
OUTDIR="${4:-/tmp/ni_parallel}"
STAGGER="${5:-5}"

VELLVM="$(pwd)/vellvm"
NIT="rocq/QC/NITests.v"

if [ ! -x "$VELLVM" ]; then
  echo "ERROR: vellvm binary not found at $VELLVM  (run 'make vellvm' first)"; exit 1
fi

mkdir -p "$OUTDIR"

# Configure the shared test file: per-process test count and timeout.
sed -i "s/Extract Constant defNumTests => \"[0-9]*\"\\./Extract Constant defNumTests => \"$PER\"./" "$NIT"
sed -i "s/timeout [0-9]* /timeout $TIMEOUT /g" "$NIT"

echo "=================================================================="
echo " NI parallel run"
echo "   processes : $NPROC"
echo "   per proc  : $PER tests   (total target ~ $((NPROC * PER)))"
echo "   timeout   : ${TIMEOUT}s per shell-out"
echo "   logs      : $OUTDIR/run_<i>.log"
echo "=================================================================="

pids=()
for i in $(seq 1 "$NPROC"); do
  VELLVM_BIN="$VELLVM" rocq top -q -w none -R rocq Vellvm -R ml/extracted Extract \
    -batch -load-vernac-source "$NIT" > "$OUTDIR/run_$i.log" 2>&1 &
  pids+=("$!")
  echo "  launched run_$i (pid $!)"
  [ "$i" -lt "$NPROC" ] && sleep "$STAGGER"
done

echo "Waiting for ${#pids[@]} processes ..."
wait

echo ""
echo "==================== AGGREGATE ===================="
total_pass=0; total_disc=0; total_fail=0
for i in $(seq 1 "$NPROC"); do
  log="$OUTDIR/run_$i.log"
  p=$(grep -aoE "Passed [0-9]+ tests" "$log" 2>/dev/null | grep -oE "[0-9]+" | head -1)
  d=$(grep -aoE "\([0-9]+ discards\)" "$log" 2>/dev/null | grep -oE "[0-9]+" | head -1)
  f=$(grep -acE "Failed after" "$log" 2>/dev/null)
  printf "  run_%-2s  passed=%-6s discards=%-5s failed=%s\n" "$i" "${p:-?}" "${d:-?}" "$f"
  total_pass=$((total_pass + ${p:-0}))
  total_disc=$((total_disc + ${d:-0}))
  total_fail=$((total_fail + f))
done
echo "---------------------------------------------------"
echo "  TOTAL   passed=$total_pass  discards=$total_disc  failed=$total_fail"
echo ""
echo "Discard breakdown (summed across all runs):"
grep -ahoE "[0-9]+ : \\(Discarded\\) \"[^\"]*\"" "$OUTDIR"/run_*.log 2>/dev/null \
  | awk -F' : \\(Discarded\\) ' '{cnt[$2]+=$1} END {for (r in cnt) printf "  %7d  %s\n", cnt[r], r}' \
  | sort -rn
echo ""
if [ "$total_fail" -gt 0 ]; then
  echo "!!! FAILURES found in:"
  grep -alE "Failed after" "$OUTDIR"/run_*.log
  echo "    (extract the .ll with:  perl -0777 -ne 'print \$1 if /<<<LLBEGIN(.*?)LLEND>>>/s' <log>)"
else
  echo "No failures."
fi
