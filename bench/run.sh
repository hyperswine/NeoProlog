#!/bin/sh
# Engine benchmarks (see docs/engine-roadmap.md).  Prints wall-clock seconds
# per workload for infera, and for swipl / scryer-prolog when installed.
set -e
cd "$(dirname "$0")"
BIN="${INFERA_BIN:-$(cd .. && cabal list-bin exe:infera 2>/dev/null || echo infera)}"
time_it() { /usr/bin/time -p sh -c "$1" 2>&1 >/dev/null | awk '/^real/ {print $2}'; }
echo "workload                 infera    swipl   scryer"
for w in "bench_nrev 3000|bench_nrev(3000)" "loop 90000|loop(90000)" "fib 25 F|fib(25,F)" "queens 8 Qs, !|once(queens(8,Qs))"; do
  iq="${w%%|*}"; pq="${w##*|}"
  printf '%s\n:q\n' "$iq?" > .q.txt
  i=$(time_it "$BIN bench.nprolog < .q.txt")
  s=$(command -v swipl >/dev/null && time_it "swipl -q -g '$pq,halt' -t halt bench.pl" || echo "-")
  c=$(command -v scryer-prolog >/dev/null && time_it "scryer-prolog -g '$pq,halt' bench.pl" || echo "-")
  printf '%-24s %7s %8s %8s\n' "$iq" "$i" "$s" "$c"
done
rm -f .q.txt
