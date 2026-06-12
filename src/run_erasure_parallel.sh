#!/usr/bin/env bash
#
# Run the erasure QuickChick test (ErasureTests.v) in parallel across N
# independent processes and aggregate the results. Same harness shape as
# run_ni_parallel.sh; see that script for the details.
#
# Usage:  ./run_erasure_parallel.sh [NPROC] [PER] [TIMEOUT] [OUTDIR] [STAGGER]
set -u
cd "$(dirname "$0")"

NPROC="${1:-8}"
PER="${2:-1000}"
TIMEOUT="${3:-5}"
OUTDIR="${4:-/tmp/erasure_parallel}"
STAGGER="${5:-5}"

VELLVM="$(pwd)/vellvm"
NIT="rocq/QC/ErasureTests.v"

if [ ! -x "$VELLVM" ]; then
  echo "ERROR: vellvm binary not found at $VELLVM  (run 'make vellvm' first)"; exit 1
fi

mkdir -p "$OUTDIR"

sed -i "s/Extract Constant defNumTests => \"[0-9]*\"\\./Extract Constant defNumTests => \"$PER\"./" "$NIT"
sed -i "s/timeout [0-9]* /timeout $TIMEOUT /g" "$NIT"

echo "=================================================================="
echo " Erasure parallel run (anchor 1: obs instrumentation conservative)"
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
  echo "!!! ERASURE MISMATCHES found in:"
  grep -alE "Failed after" "$OUTDIR"/run_*.log
  echo "    (extract the .ll with:  perl -0777 -ne 'print \$1 if /<<<LLBEGIN(.*?)LLEND>>>/s' <log>)"
else
  echo "No mismatches."
fi
