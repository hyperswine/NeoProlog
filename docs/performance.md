# Performance measurements

## Head matching and registers - 2026-10-16

The opt-in compiler now matches known head structures without duplicating their
graphs, pools repeated variable/scalar registers and delays body construction
until head acceptance. A structured-head probe avoids 80,001 head constructors;
the fixture's construction plan shrinks from 135 to 84 slots. Whole-head CLP
propagation and complete rollback retain the existing semantics.

Current paired measurements remain mixed: Bytecode is faster on the structured
list case, but slower on helper dispatch and structured heads. No general
throughput win is established. The interpreted native driver remains the public
default. All 28 compiled residency samples pass, including million-iteration
loops with live alternatives, opaque scopes and CLP state.
The [head/register report](engine-step2-head-register-2026-10-16.md) records
current source-matched samples, validation and remaining work.

## Native follow-up and first bytecode slice - 2026-10-16

This section records the foundation snapshot before the head/register changes.
The large-minefield regression is fixed. Constrained table calls now evaluate
their plain fallback on the active driver. Monotone native-store synchronization
avoids revalidating unchanged historical substitutions, and graph normalization
preserves shared grid/list suffixes. The
[foundation report](engine-step2-foundation-2026-10-16.md) records the contracts,
correctness tests, bounded-residency recheck and first opt-in bytecode slice.

Fresh CLI measurements use the same local GHC 9.8.2 `-O2` library/executable
profile and RTS `-N1`, one checked warmup and three checked timed processes.
They include startup, parsing, loading, solving and output. Timings remain local
reports rather than portable CI thresholds.

| Workload | Native before follow-up | Native after follow-up |
| --- | ---: | ---: |
| 16x16 ordinary first minefield | >30 s, timeout | 0.476 s |
| 16x16 minefield setup | not recorded | 0.451 s |
| 16x16 seeded minefield, seed 42 | not recorded | 5.844 s |
| 100-edge chain, all 5,050 pairs | 0.099 s | 0.091 s |
| Three disconnected parts, 1..16 window | 0.053 s | 0.044 s |
| Reverse 30-element list 3,000 times | 32.551 s | 19.369 s |
| Counting loop to 90,000 | 0.752 s | 0.485 s |
| Untabled fib 25 | 4.168 s | 2.694 s |
| First valid 8-queens placement | 1.311 s | 0.578 s |

Raw current samples: [applications](performance-step2-2026-10-16.jsonl) and
[CLI matrix](engine-step2-cli-2026-10-16.jsonl). The previous raw files below
remain historical provenance. Despite the recovery, general native execution
still trails the pre-migration baseline on reverse, loop, Fibonacci and queens;
that baseline used a different library optimization profile.

The separate loaded-program minefield benchmark records native setup at
0.388 s and ordinary generation at 0.432 s, versus current Reference medians
0.060 s and 0.067 s with the same `-O2` profile. It fully drains the search and
checks exact Reference parity; ordinary generation additionally checks the
bomb count and every overlapping window independently. These timings exclude
startup/parsing/loading and must not be compared directly to CLI samples.
[Raw loaded-program samples](engine-step2-minefield-2026-10-16.jsonl).

The first Step 2 compiler/VM slice preserves results but establishes no
measurable throughput gain over the interpreted native driver. It remains
opt-in while specialized head instructions, registers, control/indexing code
and load-time caches are developed.
[Three-engine samples](engine-step2-bytecode-2026-10-16.tsv).

<a id="current-native-engine-recheck---2026-10-16"></a>

## Native engine recheck before follow-up - 2026-10-16

After the public solver switched to the Step 1 native machine, three of these
application workloads were rerun with the current `-O2` library and executable,
RTS `-N1`, three requested fresh CLI samples and a 30-second process budget.
The ordinary minefield timed out on its first sample; no timing is inferred
from that failure. [Raw results for that snapshot](performance-step1-2026-10-16.jsonl)
record the runtime source hash and build profile.

| Workload | Before the earlier optimizations (s) | Optimized reference (s) | Native before follow-up (s) |
| --- | ---: | ---: | ---: |
| 16x16 ordinary first minefield | 2.163 | 0.116 | >30, timeout |
| 100-edge chain, all 5,050 reachable pairs | 0.595 | 0.032 | 0.099 |
| Three disconnected parts, 1..16 breadboard window | 0.809 | 0.037 | 0.053 |

The earlier CLP/tabling application gains remain visible for graph closure and
wide placement, but the native engine gives some of them back and introduces
a major large-minefield regression. General execution also regresses against
the [pre-migration CLI baseline](engine-baseline-2026-10-16.jsonl): reverse
6.188s -> 32.551s, loop 0.268s -> 0.752s, Fibonacci 0.463s -> 4.168s and queens
0.111s -> 1.311s. [CLI results for that snapshot](engine-step1-cli-2026-10-16.jsonl)
validate all four workloads. The historical baseline used a different library
optimization profile, so these are recorded local observations, not controlled
portable regression ratios.

Step 1's correctness and bounded-residency gates did not establish throughput
acceptance. This regression blocked Step 2 until the follow-up above resolved
it; the larger minefield is now retained in acceptance tests and CI. The
historical results below describe the optimized reference stage.

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
