#!/bin/bash
#
# erasure_corpus_check.sh — anchor-1 "erasure" differential over a corpus.
#
# For each archived program P with @main(i32 x k):
#   path A (our obs pipeline):   vellvm -interpret-obs-args <args> P
#   path B (original pipeline):  vellvm -interpret P_wrapped
# where P_wrapped renames @main to @main_orig and adds a zero-arg @main
# that calls it with <args> baked in as constants. Both paths therefore
# perform the same computation; only the obs instrumentation differs.
#
# Compared per program: termination class (OK / ERR / TIMEOUT / CRASH)
# and payload (final dvalue, or error reason). obs/partition output is
# deliberately ignored — erasure means "everything else is equal".
#
# Args are derived deterministically from the file name hash, so the
# whole campaign is reproducible from the corpus alone.
#
# Usage: ./erasure_corpus_check.sh <corpus-dir> <outdir> [jobs] [timeout-s]
set -u
CORPUS="${1:?corpus dir}"
OUT="${2:?output dir}"
JOBS="${3:-12}"
TMO="${4:-5}"
SRC="$(cd "$(dirname "$0")" && pwd)"
export VELLVM="$SRC/vellvm" TMO OUT
mkdir -p "$OUT/wrapped"
: > "$OUT/results.tsv"

check_one() {
  f="$1"
  base=$(basename "$f" .ll)
  k=$(grep -m1 'define.*@main' "$f" | grep -oP '@main\(\K[^)]*' \
      | awk -F',' '{print ($0==""?0:NF)}')
  hash=$(printf '%s' "$base" | md5sum | cut -c1-24)
  args=""
  for i in $(seq 0 $((k-1))); do
    h=$(( 16#${hash:$((i*3)):3} ))
    args="$args,$(( h % 1999 - 999 ))"
  done
  args=${args#,}
  w="$OUT/wrapped/$base.ll"
  sed 's/@main\b/@main_orig/g' "$f" > "$w"
  callargs=$(printf '%s' "$args" | sed 's/\(-\?[0-9][0-9]*\)/i32 \1/g')
  printf '\ndefine i8 @main() {\n  %%r = call i8 @main_orig(%s)\n  ret i8 %%r\n}\n' \
    "$callargs" >> "$w"

  classify() { # $1 = exit code, $2 = combined output
    if [ "$1" = 124 ]; then echo "TIMEOUT|"
    elif line=$(grep -m1 '^Program terminated with:' <<<"$2"); then
      echo "OK|${line#Program terminated with: }"
    elif line=$(grep -m1 '^Program error:' <<<"$2"); then
      echo "ERR|${line#Program error: }"
    elif line=$(grep -m1 'Fatal error: exception Failure' <<<"$2"); then
      line=${line#*Failure(\"}; echo "ERR|${line%\")*}"
    elif line=$(grep -m1 -E 'exception|rror' <<<"$2"); then
      echo "CRASH|$(head -c 150 <<<"$line")"
    else echo "CRASH|no-recognizable-output"
    fi
  }

  oA=$(timeout "$TMO" "$VELLVM" -interpret-obs-args "$args" "$f" 2>&1); rA=$?
  oB=$(timeout "$TMO" "$VELLVM" -interpret "$w" 2>&1);                  rB=$?
  A=$(classify "$rA" "$oA"); B=$(classify "$rB" "$oB")
  cA=${A%%|*}; cB=${B%%|*}
  if   [ "$A" = "$B" ] && [ "$cA" = "OK" ];     then v=MATCH
  elif [ "$cA" = TIMEOUT ] && [ "$cB" = TIMEOUT ]; then v=BOTH_TIMEOUT
  elif [ "$A" = "$B" ];                          then v=MATCH_ERR
  elif [ "$cA" = "$cB" ] && [ "$cA" = ERR ];     then v=MISMATCH_ERRMSG
  elif [ "$cA" = "$cB" ];                        then v=MISMATCH_VALUE
  else v=MISMATCH_CLASS
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$v" "$base" "$k" "$args" "$A" "$B" \
    >> "$OUT/results.tsv"
}
export -f check_one

ls "$CORPUS"/*.ll | xargs -P "$JOBS" -I{} bash -c 'check_one "$@"' _ {}

echo "==================== ERASURE SUMMARY ===================="
cut -f1 "$OUT/results.tsv" | sort | uniq -c | sort -rn
total=$(wc -l < "$OUT/results.tsv")
bad=$(grep -c '^MISMATCH' "$OUT/results.tsv")
echo "total=$total  mismatches=$bad"
if [ "$bad" -gt 0 ]; then
  echo "--- first 20 mismatches ---"
  grep '^MISMATCH' "$OUT/results.tsv" | head -20
fi
