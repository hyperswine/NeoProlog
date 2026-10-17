# Opaque control restoration and engine comparisons

This stage follows the typed builtin operand implementation. It targets the
cost of returning from `once`, negation and if-then-else while retaining their
existing isolation, failure, error and backtracking behavior. Matched local
measurements show less CPU use for scoped controls and Minesweeper, while
breadboard remains approximately unchanged. The working default-backend gate
is local representative throughput within roughly twice either SWI-Prolog or
Scryer, alongside correctness and bounded residency. Bytecode remains opt-in
until that gate is checked against the final source.

The frozen candidate runtime SHA-256 is
`b2e28dd605991249276dd563aca389a51306f82397a714dd74f2ff8c1401fb84`.
The baseline is the prior typed builtin runtime,
`d1b2cb95487c18c899925d8efd50ce25fc1848ff6136f49f69c2530986fd9ae4`,
preserved independently with matching source bytes. Full correctness and
residency checks passed. External engine checks show that the default-backend
performance gate remains unmet.

## Implementation and correctness

Successful selected opaque results can now resume their parked caller using
the child's current heap and bindings. An integer epoch tracks heap restores
and collection. When the epoch still matches scope entry and tracing is
disabled, the caller's heap prefix remains valid, so `once`, successful
conditions and DCG emission can hand over their current state without
restoring the entry snapshot and replaying accepted bindings. A changed epoch
or tracing uses the existing restore/replay path. The guard covers both
Interpreted and Bytecode execution; it is not an unconditional Bytecode-only
shortcut. Streaming `call`, minimizers, failed conditions and negation retain
their existing restoration policies.

Measured counters separately record successful `metricScopeHandoffs` and
`metricScopeReplays`. Normal timed execution leaves instruction counters
disabled. Post-timing probes establish that the handoff is exercised where
eligible and that restoration remains available after heap changes. These
counters establish path coverage, not process-memory savings.

The conservative tail-call proof now accepts closed pure control trees:
conjunction, disjunction, if-then-else, `once` and negation. It checks both
alternatives, every conditional arm and all reachable helper definitions.
Dynamic, tabled, unsafe, CLP posting and meta-called targets remain outside
this proof.
Runtime stack and argument guards still establish actual tail position and
contract/cut safety. Physical frame retirement is separate from logical fuel
reuse: `eligibleFuelReuse` retains the historical narrower proof, preserving
the existing resolution-depth policy for newly eligible scoped loops.

The complete local Haskell suite passed **380 properties / 26,230 cases**.
This includes **eight new opaque-control properties / 306 cases** and **two
new tail-control properties / 201 cases**, in addition to the prior typed
builtin coverage. All **47 LSP tests** passed without skips, CLI acceptance
passed and all **34 Python benchmark-harness tests** passed. The new harness
tests check independent models, explicit backend selection, failure and
timeout handling, duplicated or absent markers, zero/nonfinite clocks,
Scryer's CPU-only policy, positive coarse timing exclusion from the comparison
gate and alternating isolated process execution. Real engine correctness
checks remain separate from executable-double tests.

Builds and runtime correctness checks finished before matched benchmark
timing. Harness checks were repeated after the external protocol repair and
passed before the completed external rerun. Cross-platform CI remains a
separate gate; these changes are uncommitted.

The [broader bytecode acceptance runner](engine-step2-opaque-controls-bytecode-2026-10-17.tsv)
passed all **27 engine/case rows and nine positive compiled probes** across
nine fixtures. Eight probes record positive typed-builtin counts with equal
wrappers avoided. The early-fail fixture correctly records zero typed calls,
because its first `fail` prevents the later instructions from running. This
runner's existing pre-timing compiled probes make it a separate warm
acceptance check; its timings are not pooled into the matched measurements.

All **36 fresh-process residency checks** passed: the
[full Bytecode matrix](engine-step2-opaque-controls-tail-2026-10-17.jsonl)
contains 30 processes and the
[Interpreted quick comparison](engine-step2-opaque-controls-native-tail-2026-10-17.jsonl)
contains six. Every record fully drained its query, retained the frozen
runtime hash and met the existing RSS/RTS maximum-live bound of 1.5 times
prefix maxima. The matrix includes mutual recursion, retained choices,
findall, helper calls, structured arguments, CLP, tables, dynamic state and
parked compiled controls, with normal and measured million-call runs.
Bytecode peak RSS ranged from **179,650,560 to 182,861,824 bytes**, with
maximum RTS live bytes **57,162,656** and maximum measured heap size
**1,028 cells**. Interpreted peak RSS ranged from **180,617,216 to
181,682,176 bytes**, with maximum measured heap size **1,030 cells**. These
checks establish bounded residency under the existing policy, not memory
improvement against a matched baseline.

`cabal check` and `cabal sdist` passed. The package check retains the existing
`-O2` and dependency-upper-bound warnings. All 187 source-archive file
members match their working-tree bytes, including the new runners, tests and
report/evidence files. Markdown links and whitespace checks passed. CI now
runs both Python benchmark-harness test files; cross-platform CI and installed
binary deployment remain separate from this local validation.

## Workloads and measurement boundaries

The cache runner now splits the existing 300-iteration sum loop into five
fixtures. Every fixture must return exactly `45150`, with no additional
answers, residual constraints, output or errors:

| Fixture | Repeated operation |
| --- | --- |
| `controls-arithmetic` | Integer arithmetic without an opaque sub-search |
| `controls-once` | `once` chooses the first of two possible bindings |
| `controls-not` | Negation rejects a false negative-integer comparison |
| `controls-if` | A threshold at 150 exercises both then and else branches |
| `controls` | The existing combined once/negation/conditional fixture |

The combined fixture is unchanged. The split fixtures use the same loop
count, accumulator and arithmetic model. Their isolated timings make it
possible to distinguish scope costs from a general arithmetic change.
Post-timing measured probes establish compiled execution separately from
normal timing. The full `Metrics` text allows newer scope counters to be
checked without requiring newer field accessors when building an older
baseline with the identical runner.

The loaded runner also includes the existing four cross-engine core
workloads: 3,000 reversals of a 30-element list, a 90,000-iteration counting
loop, untabled Fibonacci 25 and the first eight-queens solution. These read
the existing benchmark sources and retain their outer `once`, matching the
CLI benchmark's search policy. Reverse, integer and queens models independently
check the result; the Infera runner additionally compares the complete ordered
event stream with Reference.

The four existing breadboard cases remain the real CLP acceptance workload:
RC, divider, transistor and a wide disconnected circuit. Physical geometry,
net compatibility, the independently enumerated optimum and exact Reference
placement/order must all pass. Breadboard runs compare Infera stages and
backends; they are not a SWI/Scryer translation benchmark.

## SWI and Scryer comparison protocol

`bench/runtime-compare.py` explicitly selects Infera Bytecode through the
loaded `machine-cache` runner. It does not use the Infera CLI's current
Interpreted default as a proxy for Bytecode. The companion Prolog source
translates the split control loops directly and reuses `bench/bench.pl` for
the four core algorithms.

Each sample starts a fresh process, loads its program and completes one
checked warm query before its internal clock interval. Every timed query
fully drains its selected search and passes result checks. Output and a final
checked answer occur after timing. The default batch is 100 queries for
controls and one query for core cases. Engine order reverses on alternating
rounds; all samples, source hashes and commands are retained. Zero durations
below a timer's resolution are rejected and require a larger batch.

Installed-engine probes confirmed SWI's `statistics(runtime, ...)` and
`statistics(walltime, ...)` millisecond counters. Installed Scryer does not
provide `statistics/2`; its verified `library(time)` prints loaded batch CPU
seconds to three decimal places. Scryer rows therefore leave loaded wall time
unavailable. Whole-process wall time is not substituted for a loaded clock.
An error may still produce exit status zero in Scryer, so semantic markers,
independent answers and exactly one positive CPU record are required as well
as successful process exit. Captured Scryer output also establishes that its
timer can indent the following result line and group inference counts with
underscores; parsing accommodates both while still requiring unique markers
and timing records. Timer quantization matters on short samples; batch counts
and clock policies remain visible in every row.

This is an equivalent-workload comparison with explicit overhead boundaries.
Infera timing includes event projection and its Reference ordered-stream
comparison. Prolog timing includes `findall` and independent value/queen
checks. Infera also projects the named intermediate list in the reverse
query. These operations have different representations and costs; the
comparison does not isolate VM instruction dispatch. Queens solutions may
differ across engines while satisfying the same independent board model.

The existing `bench/run.py` results, when run, remain a separate CLI scope:
startup, loading, solving and output. Its Infera executable uses the current
Interpreted default. Those figures must not be labeled Bytecode or pooled
with loaded-runtime samples.

## Results

The completed matched pass has **216 cache process records**: all five control
fixtures cold and warm under Reference, Interpreted and Bytecode, plus warm
helper-zero, structured-head and Minesweeper sanity cases under Interpreted
and Bytecode. Each engine/case/phase has three alternating baseline/candidate
pairs. The breadboard pass has **72 process records / 216 internal timed
batches**, covering all four cases under all three Infera engines with batch
30. All records passed their semantic checks and retained identical workload
and answer fingerprints across stages and engines. All **75 candidate
post-timing compiled probes** recorded positive compiled activations and typed
builtin calls, with equal wrappers avoided. Runtime, runner and fixture hashes
were unchanged at the end of the pass. No build, test or runtime/runner/fixture
edit overlapped timing, and no outliers or process samples were discarded
from these completed matched passes. Documentation was updated independently.

The [cache evidence](engine-step2-opaque-controls-cache-2026-10-17.jsonl) and
[breadboard evidence](engine-step2-opaque-controls-breadboard-2026-10-17.jsonl)
retain commands, source/fixture hashes, raw timing samples, ordered result
fingerprints and post-timing metrics. Both stages used identical updated
runners under local macOS arm64/GHC 9.8 with optimization enabled. Warm cache
controls used batch 100; cold cache and warm sanity queries used batch one.
Each breadboard process used three checked timed batches of 30 queries.
Cold means the first native/compiled query after loading; the Reference
oracle has already executed outside timing, so a cold Reference row is not
its first solve in that process. Warm queries share immutable program plans
while starting fresh query heaps, stores, tables and dynamic state.

Tables show CPU milliseconds per query, as medians of three process samples.
Breadboard uses each process's internal median before taking the median
across its three processes. Paired ratios are medians of the corresponding
candidate/baseline ratios, separately for CPU and wall. They are not ratios
of the aggregate medians. A ratio below one favors the candidate. Different
engines are contemporary context, rather than adjacent stage pairs, and batch
averages are not individual-query latency distributions. Raw metadata retains
the predeclared material-regression marker: a paired median increase exceeding
10%. Crossing this marker calls for investigation rather than silently
discarding a sample or changing the threshold.

### Split controls

| Case / phase | Baseline Bytecode CPU ms | Candidate Interpreted CPU ms | Candidate Bytecode CPU ms | Paired wall ratio | Paired CPU ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| Arithmetic / cold | 2.833 | 3.398 | 3.140 | 1.112 | 1.108 |
| Once / cold | 5.934 | 4.796 | 4.420 | 0.767 | 0.766 |
| Negation / cold | 4.241 | 4.230 | 4.014 | 0.925 | 0.929 |
| Conditional / cold | 4.605 | 4.750 | 4.163 | 0.902 | 0.902 |
| Combined / cold | 8.064 | 6.395 | 5.437 | 0.683 | 0.679 |
| Arithmetic / warm | 2.685 | 3.055 | 2.718 | 0.999 | 1.002 |
| Once / warm | 5.562 | 4.257 | 3.815 | 0.678 | 0.676 |
| Negation / warm | 4.153 | 3.742 | 3.559 | 0.856 | 0.857 |
| Conditional / warm | 4.462 | 4.262 | 3.590 | 0.805 | 0.805 |
| Combined / warm | 8.882 | 6.955 | 5.396 | 0.642 | 0.641 |

Warm Bytecode improves in all three matched pairs for each scope fixture:
once uses **32.4% less CPU**, negation **14.3% less**, the conditional **19.5%
less** and combined controls **35.9% less**, using median paired ratios.
Their CPU ratio ranges are 0.625-0.688, 0.786-0.871, 0.779-0.838 and
0.600-0.646, respectively. Arithmetic remains approximately unchanged.
Interpreted also improves on the four warm scope fixtures: median paired CPU
ratios are 0.713, 0.837, 0.817 and 0.775. The shared driver change therefore
benefits both backends.

Cold arithmetic has a 10.8% Bytecode median paired CPU increase, crossing the
nominal 10% regression marker, with mixed individual pairs ranging from 0.969
to 1.162. The unchanged Reference engine's
cold arithmetic median paired CPU ratio is 1.240, and cold combined Reference
is 1.361. Warm Reference ratios are much steadier: 0.988-1.006 on the four
split fixtures, with combined at 1.052. The small cold rows expose substantial
host variation and do not establish a general cold-start improvement. The
cold arithmetic result remains an open conservative gate, rather than being
declared harmless from the favorable warm result. Cold combined Bytecode also
has one slower pair despite its favorable median.

The deterministic post-timing probes explain the reached paths:

| Warm Bytecode fixture | Handoffs / replays | Tail calls, baseline to candidate | Max tasks, baseline to candidate | Max heap cells, baseline to candidate |
| --- | ---: | ---: | ---: | ---: |
| Arithmetic | 0 / 0 | 300 to 300 | 2 to 2 | 1,029 to 1,029 |
| Once | 300 / 0 | 0 to 300 | 301 to 2 | 1,029 to 1,026 |
| Negation | 0 / 0 | 0 to 300 | 301 to 2 | 1,029 to 1,029 |
| Conditional | 150 / 0 | 0 to 300 | 302 to 3 | 1,029 to 1,025 |
| Combined | 599 / 1 | 0 to 300 | 302 to 3 | 1,029 to 1,026 |

Negation reaches no selected-result handoff; its improvement accompanies
frame retirement. The conditional executes 150 successful conditions and
150 else branches. Combined controls exercise the restore/replay fallback
once after a heap epoch change. These counters are identical across the three
processes and cold/warm probes for the same source fixture. The baseline did
not expose handoff/replay fields; its absence is not a measured zero. Heap
cell maxima barely change, and some binding maxima increase, so lower task
counts alone do not establish lower RSS or live-memory use.

### Sanity and CLP acceptance

| Warm fixture | Baseline Bytecode CPU ms | Candidate Interpreted CPU ms | Candidate Bytecode CPU ms | Paired wall ratio | Paired CPU ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| Helper zero | 157.508 | 156.717 | 147.837 | 0.919 | 0.925 |
| Structured heads | 199.528 | 242.464 | 201.708 | 1.013 | 1.013 |
| Minesweeper 16x16 | 442.439 | 394.397 | 342.329 | 0.777 | 0.777 |

Minesweeper uses **22.3% less CPU** in the median paired comparison and
improves in all three pairs, with CPU ratios 0.726-0.784. Its probe records
269 handoffs and 36 replays; collections fall from 91 to 86, while maximum
tasks stay at 517 and maximum heap cells move from 3,414 to 3,357. This is a
local improvement against the typed-builtin baseline, rather than a general
CLP-store optimization. Helper results are mixed across pairs despite the
favorable median, and structured heads stay approximately unchanged.

| Breadboard case | Baseline Bytecode CPU ms | Candidate Interpreted CPU ms | Candidate Bytecode CPU ms | Paired wall ratio | Paired CPU ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| RC | 3.089 | 2.917 | 3.179 | 1.006 | 1.007 |
| Divider | 5.301 | 5.057 | 5.406 | 1.010 | 1.008 |
| Transistor | 11.797 | 13.843 | 11.842 | 0.996 | 0.994 |
| Wide disconnected | 12.084 | 12.956 | 12.021 | 1.005 | 1.003 |

No breadboard Bytecode speedup is established. All four cases have mixed
paired CPU samples; ranges are 0.993-1.039, 0.917-1.034, 0.993-1.013 and
0.874-1.019. Contemporary Bytecode CPU medians are 9.0% slower than
Interpreted for RC and 6.9% slower for divider, while transistor is 14.5%
faster and wide disconnected is 7.2% faster. Those contextual differences do
not constitute paired cross-backend estimates.

Breadboard probes record handoffs/replays of 2/2 for RC, 6/5 for divider and
18/5 for transistor. Wide disconnected records 0/0. Their maximum task counts
stay at 12, 14, 14 and 14; heap-cell maxima move from 1,181 to 1,178,
1,112 to 1,093, 1,242 to 1,232 and 1,029 to 1,029. The reached handoffs are a
small part of these CLP workloads and do not remove the remaining CLP-store
reconciliation and propagation costs.

### External engine gate

The completed external pass covers all nine control/core cases under explicit
Infera Bytecode, SWI and Scryer: **27 engine/case records / 81 fresh-process
samples**. All semantic checks passed, with the same frozen runtime and source
hashes throughout. Installed versions were **SWI-Prolog 10.0.2 for fat-darwin**
and **Scryer cargo 0.10.0**. An initial attempt was interrupted after observing
Scryer's indented output and grouped inference counts. Its **12 records** cover four
completed cases: eight successful Infera/SWI rows and four Scryer parser
errors. All are preserved in the
[initial evidence](engine-step2-opaque-controls-external-initial-2026-10-17.jsonl).
The entire incomplete initial attempt is excluded from performance tables,
and all nine cases are rerun under the repaired parser. This protocol repair
does not change the frozen runtime or the completed matched-stage measurements.

A positive duration of only one to five milliseconds is
descriptive evidence, not sufficient precision for a near-2x default-backend
decision. The gate requires at least 50 milliseconds of batch CPU per
engine/sample, with fixed case-specific batches and all coarse or failed
records retained. Rows expose `comparison_timing_sufficient` separately from
semantic success and record `minimum_gate_batch_cpu_seconds`. The final
external pass uses batch 6,000 for arithmetic, negation and conditional
controls; 2,000 for once and combined controls; one for reverse; 20 for
counting; five for Fibonacci; and ten for queens.

All **nine Scryer rows** and all **nine Infera rows** meet the timing-quality
gate. Six SWI rows qualify; reverse, counting and queens have only 20,
36-37 and 24 milliseconds of batch CPU, respectively, so those three SWI
rows remain descriptive. Overall, **24 of 27 rows** qualify. The following
table uses per-query CPU milliseconds as medians of three samples. Its last
column is the median of Infera/Scryer CPU ratios for corresponding rounds,
which can differ from a ratio of the displayed medians. Engine order reverses
between rounds, but these are cross-engine workload comparisons rather than
same-engine stage pairs.

| Case | Batch | Infera Bytecode CPU ms | SWI CPU ms | Scryer CPU ms | Median round CPU ratio vs Scryer |
| --- | ---: | ---: | ---: | ---: | ---: |
| Arithmetic controls | 6,000 | 2.519 | 0.01583 | 0.04267 | 58.4x |
| Once controls | 2,000 | 3.756 | 0.09350 | 1.48850 | 2.52x |
| Negation controls | 6,000 | 3.648 | 0.02133 | 0.05783 | 63.9x |
| Conditional controls | 6,000 | 3.738 | 0.02167 | 0.05800 | 64.5x |
| Combined controls | 2,000 | 5.663 | 0.11250 | 1.54250 | 3.67x |
| Reverse 3,000 x 30 elements | 1 | 20,155.034 | 20.00000 (coarse) | 93.00000 | 220.0x |
| Counting 90,000 | 20 | 445.539 | 1.85000 (coarse) | 8.40000 | 53.7x |
| Fibonacci 25 | 5 | 2,317.739 | 10.40000 | 28.20000 | 82.1x |
| Eight queens, first solution | 10 | 572.377 | 2.40000 (coarse) | 5.40000 | 106.0x |

The [final external evidence](engine-step2-opaque-controls-external-2026-10-17.jsonl)
retains every sample, result, command, binary/source hash, engine version and
timing-quality flag. No samples were dropped from this completed rerun.
Scryer exposes no loaded wall clock in this runner; all conclusions here use
CPU, with wall fields explicitly unavailable for Scryer.

The default-backend performance gate is **unmet**. Once is closest to Scryer,
at 2.52x the CPU in the median round comparison, with individual ratios
2.49-2.60. The remaining Scryer comparisons range from 3.67x for combined
controls to 220x for reverse. Every Scryer comparison has sufficient batch
duration, and the six sufficiently timed SWI comparisons also remain far
outside 2x, with median round ratios approximately 40-221x. The three coarse
SWI rows do not support a precise near-2x assessment. Lower local scope costs
are useful progress, but they do not establish competitive general throughput.
Bytecode therefore remains opt-in.

## Next bounded optimization candidate

Ground-integer expression plans for `is/2` and ordinary numeric comparisons
are a source-grounded next candidate. The current
[operand materializer](../src/Infera/Machine/Bytecode.hs) still builds a heap
graph for an arithmetic expression. The
[typed builtin driver](../src/Infera/Machine/Control.hs) exports that graph
back to `Term`; the [shared arithmetic handler](../src/Infera/Machine/Builtins.hs)
walks the persistent substitution and evaluates it. `is/2` then imports its
scalar result and performs native unification. The arithmetic-only fixture
repeats two `is` operations and one ordinary comparison per loop iteration.
A guarded expression plan could evaluate integer operators from native values
without constructing/exporting the RHS syntax graph, while retaining the
existing path for unsupported values, errors and tracing.

This identifies work present in the reached source path; it is not a profile
attributing the measured engine gap to that work, and it does not promise a
2x target. Predicate calls, head matching, fresh-variable allocation and the
persistent substitution mirror would remain. Native arithmetic writes already
avoid extra CLP reconciliation when no watched variable changes, as shown by
the [native CLP boundary](../src/Infera/Machine/CLP.hs). Incremental CLP change
tracking remains a separate candidate for breadboard and other constraint
workloads; it would not by itself remove the ordinary arithmetic fixture's
remaining execution costs.
