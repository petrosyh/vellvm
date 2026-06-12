#!/bin/bash
# Optional measurement instrument for NI test campaigns: a drop-in
# replacement for ./vellvm that archives every .ll argument into
# $NI_CORPUS_DIR (content-hash filenames dedup the baseline/partner
# reruns of the same program), then execs the real binary.
#
# Not needed to reproduce test *results* — only to collect the corpus
# of generated programs for statistics (see ni_corpus_stats.py).
#
# Usage:
#   cd src
#   mv vellvm vellvm.real && cp ni_corpus_wrapper.sh vellvm
#   NI_CORPUS_DIR=$HOME/ni_corpus/programs ./run_ni_parallel.sh ...
#   # afterwards: rebuild (make vellvm) or mv vellvm.real back.
d="${NI_CORPUS_DIR:-/tmp/ni_corpus/programs}"
mkdir -p "$d"
for a in "$@"; do
  case "$a" in
    *.ll)
      h=$(md5sum "$a" 2>/dev/null | cut -d' ' -f1)
      [ -n "$h" ] && [ ! -e "$d/$h.ll" ] && cp "$a" "$d/$h.ll" 2>/dev/null
      ;;
  esac
done
exec "$(dirname "$0")/vellvm.real" "$@"
