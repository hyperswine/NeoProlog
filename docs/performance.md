# Performance changes - 2026-10-15

## Current native engine recheck - 2026-10-16

After the public solver switched to the Step 1 native machine, three of these
application workloads were rerun with the current `-O2` library and executable,
RTS `-N1`, three requested fresh CLI samples and a 30-second process budget.
The ordinary minefield timed out on its first sample; no timing is inferred
from that failure. [Current raw results](performance-step1-2026-10-16.jsonl)
record the runtime source hash and build profile.

| Workload | Before the earlier optimizations (s) | Optimized reference (s) | Current native (s) |
| --- | ---: | ---: | ---: |
| 16x16 ordinary first minefield | 2.163 | 0.116 | >30, timeout |
| 100-edge chain, all 5,050 reachable pairs | 0.595 | 0.032 | 0.099 |
| Three disconnected parts, 1..16 breadboard window | 0.809 | 0.037 | 0.053 |

The earlier CLP/tabling application gains remain visible for graph closure and
wide placement, but the native engine gives some of them back and introduces
a major large-minefield regression. General execution also regresses against
the [pre-migration CLI baseline](engine-baseline-2026-10-16.jsonl): reverse
6.188s -> 32.551s, loop 0.268s -> 0.752s, Fibonacci 0.463s -> 4.168s and queens
0.111s -> 1.311s. [Current CLI results](engine-step1-cli-2026-10-16.jsonl)
validate all four workloads. The historical baseline used a different library
optimization profile, so these are recorded local observations, not controlled
portable regression ratios.

Step 1's correctness and bounded-residency gates do not establish throughput
acceptance. Profile and resolve the large-minefield regression before beginning
Step 2 bytecode implementation; preserve this workload in future performance
checks. The historical results below describe the optimized reference stage,
not the performance of today's public native solver.

## Earlier CLP and tabling measurements

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
