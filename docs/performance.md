# Performance changes - 2026-10-15

Local measurements on macOS arm64 with GHC 9.8.2 and Cabal's default library
optimisation profile (-O1). The executable uses the unchanged -O2 build options
and each benchmark runs with +RTS -N1. Before means the saved executable and
breadboard model immediately before these performance changes; both include the
prior inference work. These are working-tree measurements, not release claims.

Each successful entry is the median of three fresh CLI processes, including
startup, parsing, loading, solving and output. The first launch after rebuilding
had extra overhead; all samples are retained in the [raw results](performance-2026-10-15.jsonl). Timings
are not cold-start guarantees or CI thresholds. Timeout cases stop after the
first eight-second timeout.

| Workload | Before (s) | After (s) | Before / after |
|---|---:|---:|---:|
| 16x16 minefield constraint setup | 1.579 | 0.077 | 20.6x |
| 10x10 seeded minefield, seed 42 | 0.404 | 0.140 | 2.9x |
| 16x16 ordinary first minefield | 2.163 | 0.116 | 18.6x |
| 16x16 seeded minefield, seed 42 | >8.000 | 2.354 | >3.4x |
| Breadboard rc | 0.031 | 0.031 | 1.0x |
| Breadboard div | 0.027 | 0.033 | 0.8x |
| Breadboard tri | 0.035 | 0.036 | 1.0x |
| 100-edge chain, one start | 0.018 | 0.016 | 1.1x |
| 200-edge chain, one start | 0.039 | 0.019 | 2.0x |
| 100-edge chain, all 5,050 reachable pairs | 0.595 | 0.032 | 18.4x |
| Three disconnected parts, 1..16 breadboard window | 0.809 | 0.037 | 21.9x |

The tiny standard breadboard examples stay around startup/load scale; some
samples are slightly slower. The wider placement model, long sums and graph
closure show the larger gains. The seeded 16x16 case remains much more expensive
than ordinary ordering: faster propagation does not remove search sensitivity.

## What changed

- Linear bounds maintain aggregate contributions instead of rescanning every
  other coefficient for each variable.
- Persistent dependency queues wake affected constraints. Initial domain lists
  are batched; active constraints keep sequential posting to preserve error order.
- Global all-different uses fixed-value exclusion, Hall intervals and bounded
  finite matching. Propagation budgets limit effort without excluding answers.
- Reified integer relations and absolute-value bounds let breadboard scoring
  constrain partial placements before branch-and-bound labeling.
- Eligible positive same-variant linear recursion consumes delta answer batches.
  Other tabling shapes, contracts, effects and constraints retain the general
  evaluator, with fallback for unexpected errors or exhaustion.

Stronger pruning can change labeling order and tied winning placements. The
bounded tests compare solution sets and optimum costs; eligible delta tabling
also compares exact ordered observations with the retained general evaluator.

## Reproduce

```sh
cabal build all --offline
python3 test/bench.py "$(cabal list-bin exe:infera)" --runs 3 --timeout 8
```

Select one workload with `--case path-all-100`. To compare versions,
save the old executable and old breadboard source before rebuilding, then pass
that source through `--breadboard OLD_MODEL` when benchmarking the old executable.
The harness omits the shipped one-line entry queries. It validates bomb counts,
dimensions, window caps and graph answers before accepting a timing sample.
The wide breadboard fixture uses three unrelated two-pin parts and a 1..16 window.

`test/ReferenceCLP.hs` freezes the previous full-scan store as a differential
oracle. Generated checks cover initially infinite bounds, aliases, nonlinear
transitions, reification, absolute values, global constraints, and both optimum
searches. Breadboard tests check independent costs and exhaustive bounded
placements; tabling tests compare ordered legacy observations and graph closure.
