# Performance measurements

See the [current engine guide](2026-10-17-ENGINE.md),
[dated report index](README.md), and
[raw data conventions](data/README.md). The newest results appear first;
the earlier sections preserve measurements from previous engine stages.

## A week over the record - 2026-10-30

`455fe74` is what the tree was on 2026-10-23: before the pinned store, the
program image, the clause instruction stream and the native JIT. Checked
`core-major --batch 20` medians, three interleaved samples per column, both
builds at `-O2` on this host:

| Case | a week ago ms | now ms | CPU | Allocation |
| --- | ---: | ---: | ---: | ---: |
| core-loop | 8.850 | 0.052 | 168.7x | 12.97 -> 8.57 MB (-34%) |
| core-nrev | 8.521 | 0.812 | 10.5x | 19.39 -> 10.11 MB (-48%) |
| liveness | 11.704 | 2.974 | 3.9x | 18.09 -> 15.50 MB (-14%) |
| breadboard-rc | 1.922 | 0.704 | 2.7x | 13.70 -> 12.52 MB (-8.6%) |
| core-queens | 8.537 | 3.427 | 2.5x | 20.29 -> 14.77 MB (-27%) |
| breadboard-div | 2.357 | 1.785 | 1.3x | 15.83 -> 14.66 MB (-7.4%) |
| breadboard-tri | 4.523 | 3.496 | 1.3x | 25.76 -> 24.63 MB (-4.4%) |
| table-cycle | 0.068 | 0.053 | 1.3x | 8.87 -> 8.82 MB (-0.5%) |
| core-fib | 38.216 | 31.583 | 1.2x | 67.81 -> 82.30 MB (+21%) |
| controls | 0.145 | 0.121 | 1.2x | 9.10 -> 9.11 MB |
| deep-index | 2.946 | 2.620 | 1.1x | 18.91 -> 19.01 MB |
| table-cycle240 | 1.022 | 0.928 | 1.1x | 14.35 -> 13.77 MB |
| breadboard-wide | 10.896 | 9.932 | 1.1x | 52.17 -> 51.10 MB |
| guards | 2.111 | 1.999 | 1.1x | 17.56 -> 18.17 MB |
| minefield-16 | 23.338 | 22.491 | 1.04x | 117.43 -> 117.10 MB |

Nothing got slower. The tail is the constraint solver and the guard/index
paths, which the week's work did not touch, and `core-fib`, which is outside
the JIT fragment and so keeps its interpreter allocation.

The four standard cases against the reference engines, same week and same
harness ([core_external.py](../bench/core_external.py), batch 100, checked
results, startup and loading excluded), medians summed to per-query CPU:

| Case | SWI ms | Scryer ms | week ms | now ms |
| --- | ---: | ---: | ---: | ---: |
| core-nrev | 0.869 | 3.100 | 8.521 (9.8x SWI) | 0.812 (0.93x SWI, 0.26x Scryer) |
| core-loop | 1.859 | 8.440 | 8.850 (4.8x SWI) | 0.052 (0.03x SWI, 0.01x Scryer) |
| core-fib | 10.517 | 28.530 | 38.216 (3.6x SWI) | 31.583 (3.00x SWI, 1.11x Scryer) |
| core-queens | 2.450 | 5.280 | 8.537 (3.5x SWI) | 3.427 (1.40x SWI, 0.65x Scryer) |

A week ago every standard case was 3.5x to 9.8x behind SWI and 1.0x to 2.5x
behind Scryer. `core-nrev` is now level with SWI and ahead of Scryer, and
`core-loop` is far ahead of both; `core-queens` is still 1.4x behind SWI and
`core-fib` 3.0x, which is the fragment work the JIT report names next.

Raw records: [jsonl](data/jsonl/engine-week-2026-10-30.jsonl),
[TSV](data/tsv/engine-week-2026-10-30.tsv), and the external numbers in
[TSV](data/tsv/engine-external-2026-10-30.tsv).

## Native JIT reachable end to end - 2026-10-30

The [activation report](2026-10-30-JIT-ACTIVATION.md) records the three
defects that kept every compiled kernel from running: matchers that
compared surface operators against internal names, invocation reading
capacity from the fresh-variable counter, and a trailing boundary older
than the JIT entry top so a bailout could not undo a binding. With them
fixed, and with kernels restricted to atomic elements so that the occurs
check stays with the interpreter, checked `core-major --batch 20` medians
fall 90.3% on reverse (10.3x), 99.4% on the counting loop (168.8x) and
60.0% on 8-queens (2.5x) against `74c1740`, with allocation per query down
48%, 34% and 27%. Fibonacci has no kernel and shows the interpreter gain
alone at 16.8%, with 21.4% more allocation. The same report halves the
cost of entering a kernel, to 15 ns per call, and locates but does not
explain the 88-byte-per-call allocation the tree path picked up since the
release. The full suite passes with the JIT enabled.

## Compiled arithmetic plans - 2026-10-19

The [arithmetic plans report](2026-10-19-ARITH-PLANS.md) records
compiled plans for flat arithmetic (slot or immediate, and one operator
over slots and immediates) in `is` and comparisons. Plans run directly on
immediate integer words and fall back to the general evaluator on any
miss. On a loaded machine, batch-20 CPU fell 10-12% on Fibonacci, 5-9% on
loop and about 6% on queens versus `e47bc65`, with reverse (no
arithmetic) flat as the control. GHC allocation is unchanged.

## Allocation-free clause selection - 2026-10-19

The [clause selection report](2026-10-19-CLAUSE-SELECTION.md)
records Core clause selection from precomputed, shared results, with an
unboxed retry cursor for clause choices. Ticky shows zero selection
allocation on reverse, loop, Fibonacci and queens. GHC allocation falls
24-43% on those workloads and 56% on a nested-decision case. CPU is flat
to +3% on the four major cases and 40% lower on the nested-decision case.

## Plain calls and the choice stack - 2026-10-19

The [control stacks report](2026-10-19-CONTROL-STACKS.md) records
checked loaded-query CPU 9-16% below `1a97539` on reverse, loop, Fibonacci
and queens, with 27-40% less GHC allocation. Engines are now compared up to
renaming of variables, which removed the Core's fresh-id bookkeeping and
exposed a `findall` copy bug in the reference and legacy machine, now fixed.
An unboxed continuation-frame stack was measured 5-14% slower than keeping
continuations as GHC values and was not adopted. A current profile places
most Core time in head matching, term construction, arithmetic and dispatch.

## Reusable Core slots and tail frames - 2026-10-18

The [profile and reuse report](2026-10-18-ENGINE-SLOTS.md) records one
fresh activation and 90,000 reused tail frames in the checked loop. CPU improves
4.3% there, but reverse takes 12.1% more CPU and GHC allocation rises on both.
The measured slot-reuse snapshot takes 1.21x Scryer on loop and 3.19x on reverse; SWI remains
5.42-11.33x faster on these cases. Breadboard and Minesweeper are near baseline.
The measured snapshot passed 440 properties, 477 forced-collection parity queries,
CLI acceptance, 61 editor tests and 56 harness tests. The combined tree after
subsequent diagnostic/CLP updates passes 443 properties and 487 parity queries
with a fresh isolated build. This iteration establishes reuse, not a general
throughput win.

## Before slot reuse: Core versus SWI and Scryer - 2026-10-18

The [fresh external comparison](2026-10-18-ENGINE-EXTERNAL.md) records
GC-inclusive loaded-query CPU at 1.26-2.77x Scryer and 3.92-10.09x SWI on
reverse, loop, Fibonacci and queens. Three of four meet the roughly-2x target
relative to Scryer; reverse remains outside it. End-to-end CLI times are closer
because startup/loading are included. The report keeps those scopes separate,
corrects SWI's GC-excluding compatibility timer, and records source/binary
identities, checked results and complete raw samples. External CLP and tabling
performance remain unmeasured.

## Mutable CLP propagation - 2026-10-18

The [mutable propagation report](2026-10-18-ENGINE-MUTABLE-CLP.md)
records native mutable domains, linear reduction and scheduling with undo
marks and immutable answer snapshots. Checked 16x16 Minesweeper generation
falls from 33.7 ms to 22.3 ms with 39% less allocation. Breadboard allocates
2-14% less but takes 7-13% more CPU; complex reducers still use a persistent
bridge. All 429 properties and 416 forced-collection parity queries pass.
The report includes native-path counters, deterministic memory evidence and
remaining rollback-history limits.

## Four Core designs - 2026-10-18

The [first implementation report](2026-10-18-ENGINE-MAJOR.md) records
native constraint search, deeper clause decisions, precise activation liveness
and delta tabling. Checked loaded-program samples show 7.16x faster nested
dispatch and 23.48x faster 240-node closure; guard dispatch improves about 15%.
Dead activation cells are reclaimed, while Breadboard and Minesweeper remain
near baseline. Several ordinary workloads still take 2-6% more CPU. The report
keeps those regressions, validation boundaries and remaining CLP work explicit.

## Reverse construction, matching and collection - 2026-10-17

The [reverse follow-up](2026-10-17-ENGINE-REVERSE.md) records a 20% reduction
in loaded-program CPU time, 38% less GHC allocation and 17% less maximum
residency against `e3082b3`. Checked CLI reverse falls from 0.507 s to
0.414 s, versus SWI 0.068 s and Scryer 0.174 s. The full 391-property
Haskell suite, 296 forced-collection example/parity queries, CLI acceptance,
61 LSP tests and 34 harness tests pass. Individual samples and provenance
are linked from the report.

## Diagnosis and the new core - 2026-10-17

The [engine diagnosis](2026-10-17-ENGINE-DIAGNOSIS.md) profiles the current
machine (15-45 KB of allocation per inference, a flat profile, 50-200x the
CPU of Scryer), attributes the cost to the representation, and records the
first slice of the replacement core in `src/Infera/Core/`: unboxed tagged
cells, a trail, choice points without snapshots, compiled heads and
heap-native arithmetic. By the end of the day the core covered tabling,
dynamic facts, `minimize` and constraints, passed the whole suite, and became
the public engine behind `Infera.Engine.solveQuery` (with fallback to the
machine). The validated CLI harness then recorded reverse 0.700 s, loop
0.030 s, fib 0.068 s and queens 0.030 s against the machine's 20.2 s,
0.45 s, 2.3 s and 0.57 s; SWI and Scryer figures are in the report. The
sections below are the earlier history.

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
The [head/register report](2026-10-16-ENGINE-STEP2-HEAD-REGISTER.md) records
current source-matched samples, validation and remaining work.

## Native follow-up and first bytecode slice - 2026-10-16

This section records the foundation snapshot before the head/register changes.
The large-minefield regression is fixed. Constrained table calls now evaluate
their plain fallback on the active driver. Monotone native-store synchronization
avoids revalidating unchanged historical substitutions, and graph normalization
preserves shared grid/list suffixes. The
[foundation report](2026-10-16-ENGINE-STEP2-FOUNDATION.md) records the contracts,
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

Raw current samples: [applications](data/jsonl/performance-step2-2026-10-16.jsonl) and
[CLI matrix](data/jsonl/engine-step2-cli-2026-10-16.jsonl). The previous raw files below
remain historical provenance. Despite the recovery, general native execution
still trails the pre-migration baseline on reverse, loop, Fibonacci and queens;
that baseline used a different library optimization profile.

The separate loaded-program minefield benchmark records native setup at
0.388 s and ordinary generation at 0.432 s, versus current Reference medians
0.060 s and 0.067 s with the same `-O2` profile. It fully drains the search and
checks exact Reference parity; ordinary generation additionally checks the
bomb count and every overlapping window independently. These timings exclude
startup/parsing/loading and must not be compared directly to CLI samples.
[Raw loaded-program samples](data/jsonl/engine-step2-minefield-2026-10-16.jsonl).

The first Step 2 compiler/VM slice preserves results but establishes no
measurable throughput gain over the interpreted native driver. It remains
opt-in while specialized head instructions, registers, control/indexing code
and load-time caches are developed.
[Three-engine samples](data/tsv/engine-step2-bytecode-2026-10-16.tsv).

<a id="current-native-engine-recheck---2026-10-16"></a>

## Native engine recheck before follow-up - 2026-10-16

After the public solver switched to the Step 1 native machine, three of these
application workloads were rerun with the current `-O2` library and executable,
RTS `-N1`, three requested fresh CLI samples and a 30-second process budget.
The ordinary minefield timed out on its first sample; no timing is inferred
from that failure. [Raw results for that snapshot](data/jsonl/performance-step1-2026-10-16.jsonl)
record the runtime source hash and build profile.

| Workload | Before the earlier optimizations (s) | Optimized reference (s) | Native before follow-up (s) |
| --- | ---: | ---: | ---: |
| 16x16 ordinary first minefield | 2.163 | 0.116 | >30, timeout |
| 100-edge chain, all 5,050 reachable pairs | 0.595 | 0.032 | 0.099 |
| Three disconnected parts, 1..16 breadboard window | 0.809 | 0.037 | 0.053 |

The earlier CLP/tabling application gains remain visible for graph closure and
wide placement, but the native engine gives some of them back and introduces
a major large-minefield regression. General execution also regresses against
the [pre-migration CLI baseline](data/jsonl/engine-baseline-2026-10-16.jsonl): reverse
6.188s -> 32.551s, loop 0.268s -> 0.752s, Fibonacci 0.463s -> 4.168s and queens
0.111s -> 1.311s. [CLI results for that snapshot](data/jsonl/engine-step1-cli-2026-10-16.jsonl)
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
had extra overhead; all samples are retained in the [raw results](data/jsonl/performance-2026-10-15.jsonl). Timings
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
