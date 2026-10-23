# Typed builtin operands - 2026-10-17

This stage follows published operand dispatch and LSP fixes,
[`4a78805`](https://github.com/hyperswine/NeoProlog/commit/4a78805e7dece86f9a41fc1563fdd53452d2b211).
It gives compiled first-order builtins their arguments directly, avoiding a
callable heap wrapper and the ordinary goal dispatcher. Bytecode remains
opt-in. The final frozen runtime passed the full local correctness suite.
Matched local measurements show a clear control improvement and a wide
breadboard improvement, alongside a Minesweeper regression. The remaining
breadboard results are mixed, so this is not a general default-backend gate.

## Implementation and semantic boundaries

The compiler recognizes 18 builtin tags at their exact supported arities:
unification, equivalence, disequality, `is`, four ordinary comparisons, six
finite-domain relations, domain membership, `all_different`, `all_distinct`
and reification. `BuiltinCall` contains a typed dispatch tag, one immutable
`OperandPlan` for all arguments and a lazy ordinary invocation plan used for
tracing. Other calls, malformed arities and dynamic callable values retain
their existing dispatch. Builtin precedence over same-named user predicates
is preserved.

Every argument shares one dense source-local layout and construction schedule.
Final argument roots count as uses in temporary-register allocation, so a
later argument cannot overwrite a temporary still needed by an earlier root.
Sparse source IDs retain their original logical identities. Materialization
does one strict environment lookup, including for ground plans, and retains
the existing bounded small-local reads, scalar/constructor validation,
single-instruction fast paths and child-read-before-overwrite order. Pending
code retains logical IDs and immutable plans; operand heap handles do not
escape across a driver or collection boundary.

The driver owns a checkpoint spanning operand construction and the semantic
operation. Rejection, solver errors and heap errors restore that prefix,
including scalar/constructor intern additions. Successful unification uses
the existing native heap/CLP boundary. `is` exports only its raw RHS, evaluates
with the shared arithmetic helper and imports the resulting scalar directly
before native unification. Remaining tags export their raw argument forest
and reuse the existing comparison, domain and CLP posting helpers. Persistent
CLP reconciliation and its propagation order remain in place.

This is a bounded first step: it removes callable wrappers and generic builtin
selection, rather than replacing every raw syntax export or the persistent
CLP store. Labeling, meta-calls, IO and other unsupported operations continue
through existing handlers. Traced execution deliberately materializes the
ordinary goal so existing source locations, call/exit/fail events and error
policies remain exact. Normal and measured untraced bytecode use typed
dispatch. New measured counters count typed builtin calls and callable
wrappers avoided; normal timing runs leave counters disabled.

Counter semantics remain bounded. `metricBodyGoalsMaterialized` counts a
reached invocation or operand plan, while body-allocation instructions count
the operand plan's source construction schedule. Arithmetic result scalars
and CLP helper allocations remain outside that instruction count, following
the existing metric policy. Bytecode instructions add one typed dispatch
opcode plus operand instructions; wrappers avoided count one per typed
attempt, including rejected calls. Sampling occurs after the atomic operation,
so rejected temporary allocations can disappear before a high-water sample.
These counters do not establish peak-memory parity or RSS reduction. Tracing
uses the ordinary fallback and records no typed calls. Collection does not
run inside the operand transaction; the surrounding driver boundaries retain
the necessary roots.

## Correctness validation

The frozen candidate runtime SHA-256 is
`d1b2cb95487c18c899925d8efd50ce25fc1848ff6136f49f69c2530986fd9ae4`.
The complete local Haskell suite passed **370 properties / 25,723 cases**,
including **nine new typed-builtin properties / 705 cases**. All **47 LSP
tests**, CLI acceptance checks and **20 Python benchmark-harness tests** also
passed. Builds and correctness tests finished before timing; earlier-stage
results do not substitute for the frozen candidate.

Generated checks compare Reference, Interpreted, normal bytecode and measured
bytecode. They compare the full ordered event stream, raw substitution
direction and IDs, every CLP store/scheduler field, fresh-variable counts,
output, dynamic facts and table metadata. Float comparisons preserve exact
bits in the test representation. Independent arithmetic and finite-domain
models check valid answers, avoiding reliance only on shared implementation
helpers.

Coverage includes sparse aliases inside opaque controls, arithmetic error
priority, malformed operands, CLP contradictions and rollback, ordinary
builtin precedence, unsupported arities, dynamic predicates and tables.
Multi-root operand tests compare construction with source import, protect
shared temporaries, reject stale/missing roots and verify atomic failure.
Frozen and interleaved checkpoints retain independent results, and traced
bytecode must retain exact interpreted traces.

The [broader bytecode acceptance runner](data/tsv/engine-step2-builtin-operands-bytecode-2026-10-17.tsv)
passed all **27 engine/case rows and nine positive compiled probes** across
nine fixtures. Eight probes also have positive typed-builtin counts and equal
wrapper counts. The early-fail-body fixture intentionally records zero typed
calls: its first `fail` prevents later builtin instructions from executing.
This runner retains its existing pre-timing compiled probes, so its results
are a separate warm acceptance gate and are not pooled into the matched
cache/breadboard measurements below.

All **36 fresh-process residency checks** passed: the [full bytecode matrix](data/jsonl/engine-step2-builtin-operands-tail-2026-10-17.jsonl)
contains 30 processes and the [interpreted quick comparison](data/jsonl/engine-step2-builtin-operands-native-tail-2026-10-17.jsonl)
contains six. Each fully drained and met the existing RSS/RTS maximum-live
bound of 1.5 times prefix maxima. The bytecode matrix covers mutual recursion,
retained choices, findall, helper calls, structured arguments, CLP, tables,
dynamic state and parked compiled controls, including normal and measured
million-call runs. Every measured bytecode sample recorded positive typed
calls with equal wrappers avoided; ordinary counters stayed zero. Compiled
peak RSS ranged from 176,439,296 to 179,617,792 bytes, with maximum measured
heap size 1,028 cells. These establish bounded residency under the existing
policy, not memory improvement against a matched baseline. All records retain
the frozen runtime hash and full commands. Cross-platform CI remains a
separate gate; this follow-up is uncommitted.

`cabal check` and `cabal sdist` passed. The package check retains the existing
`-O2` and dependency-upper-bound warnings. All source-archive members matched
the working-tree bytes, including the new parity tests and six report/evidence
files. Report links and whitespace checks passed.

## Matched benchmark protocol

The baseline runtime is exactly `4a78805`, with all 27 Haskell source files
verified against that commit's Git blob IDs. Its runtime SHA-256 is
`497c22dbae85ba4c09d61ad6aca50c71315a6144d81d79d3e843cc8aa058d6d1`.
Both stages use byte-identical updated cache and breadboard runner sources,
plus identical Minesweeper and breadboard fixtures. Local builds use macOS
arm64, GHC 9.8.2 and `-O2`. No build, test or production edit overlaps timing.
The orchestrator hashes sorted `src/**/*.hs` relative paths and bytes, each
separated with NUL, before and after the complete pass; runner/fixture bytes
must also remain unchanged.

The focused pass contains **72 cache fresh-process records**. Controls run
cold with batch one and warm with batch 100 under Reference, Interpreted and
bytecode. Helper zero, structured heads and Minesweeper 16x16 run warm with
batch one under Interpreted and bytecode. Each engine/case/phase has three
baseline/candidate pairs, alternating baseline-first and candidate-first.
No process samples are discarded. Every warm process executes one checked
query outside timing; every cold native/compiled process times its first
query. Reference already ran its oracle, so its cold label does not mean its
first execution in the process.

Breadboard runs all four cases under Reference, Interpreted (the runner's
`machine` label) and bytecode. Each engine/case has three alternating paired
processes per stage: **72 process records / 216 internal timed batches**.
Each process executes one checked warm query, then three checked batches of
30 fresh queries. Engine/case filtering makes corresponding stage processes
adjacent instead of comparing long stage blocks. Parsing, inference and the
independent optimum calculation stay outside timing.

Every timed query fully drains, projects and checks its ordered result against
Reference. Integer/grid models independently check cache cases; breadboard
checks physical geometry, net compatibility, the enumerated optimum and exact
Reference placement/order. Warm batching passes distinct nonces through the
existing `NOINLINE` execution boundary and cycles unused logical roots through
bases 2-5. Each query starts fresh heap, persistent store, table and dynamic
state; only immutable program plans are shared. Batch averages are throughput
samples, rather than individual query latency distributions.

In the two matched-stage runners, compiled probes now run after the
corresponding timing. Shared runners
emit the complete `Metrics` representation, allowing the exact older baseline
to compile without newer metric accessors. The orchestrator requires positive
candidate typed-builtin calls and equal wrappers-avoided counts for each
bytecode cache probe and every breadboard post-timing bytecode probe. It also
checks workload and answer fingerprints across both stages and engines.
Instruction counters are disabled during timed execution. A positive measured
probe establishes path coverage separately from the timing sample.

The [cache evidence](data/jsonl/engine-step2-builtin-operands-cache-2026-10-17.jsonl) stores
per-query and total batch CPU/wall times, commands, stage order, runtime and
runner/fixture hashes, semantic checks and post-timing metrics. The
[breadboard evidence](data/jsonl/engine-step2-builtin-operands-breadboard-2026-10-17.jsonl)
also retains each complete TSV output and its parsed internal samples.
Comparisons use medians of corresponding candidate/baseline paired
ratios for CPU and wall time, with contemporary Reference/Interpreted samples
to expose host drift. A ratio of aggregate medians can differ from the median
paired ratio and will not be substituted for it.

## Acceptance measurements

The complete focused pass succeeded: **72 cache records, 72 breadboard
records and 216 breadboard timed batches**. Every result passed its semantic
checks. Workload and answer fingerprints match across stages and engines;
the final runtime, runner and fixture hashes equal their frozen inputs. All
**51 candidate post-timing probes** recorded positive typed-builtin counts,
with one avoided wrapper per typed attempt. No outliers were dropped.

The tables report CPU milliseconds per query: medians of three process
samples for cache, and medians of the three per-process internal medians for
breadboard. Paired ratios use corresponding same-engine baseline/candidate
processes; ratios below one favor the candidate. Contemporary Interpreted
medians give useful context, but different engines run in separate groups
and are not adjacent stage pairs. Batch averages are not per-query latency
percentiles.

### Controls and sanity cases

| Case / phase | Baseline bytecode CPU ms | Interpreted CPU ms | Typed bytecode CPU ms | Paired wall ratio | Paired CPU ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| Controls / cold | 17.067 | 12.364 | 10.406 | 0.675 | 0.681 |
| Controls / warm, batch 100 | 13.215 | 12.315 | 10.990 | 0.830 | 0.832 |
| Helper zero / warm | 237.647 | 228.352 | 213.325 | 0.822 | 0.836 |
| Structured heads / warm | 321.306 | 334.002 | 303.160 | 0.953 | 0.944 |
| Minesweeper 16 / warm | 617.667 | 674.156 | 700.607 | 1.261 | 1.114 |

Warm controls improve in all three bytecode pairs: CPU ratios range
**0.795-0.945**, with median **0.832** (16.8% less CPU); wall ratios range
0.791-0.953. Contemporary Reference and Interpreted control CPU paired
medians are 0.986 and 0.987, respectively. The bytecode gain therefore has
more support than a general host speed change. Its contemporary median
CPU is 10.990 ms/query versus Interpreted's 12.315 ms, clearing the previous
local warm-control regression. Cold control bytecode CPU also improves in
all three pairs, with ratios 0.578-0.742.

The control post-timing probe records **1,800 typed attempts / 1,800 avoided
wrappers** per query. Operand source-allocation instructions fall from
3,900 to 2,100. Reached invocation/operand plans stay at 2,100, and the
combined bytecode-instruction count stays at 6,304: the extra typed dispatch
opcode replaces the removed callable constructor in that accounting.
These are path/allocation witnesses, not a CPU instruction count.

Helper and structured-head bytecode CPU improve in all three pairs. The
structured-head median gain is modest and its Interpreted control also
improves, so it should not be attributed entirely to typed dispatch. Helper
Interpreted CPU instead regresses in two pairs; contemporary engine timing
and raw samples are retained rather than normalized away.

**Minesweeper regresses in all three bytecode pairs**: CPU ratios are
1.239, 1.039 and 1.114; wall ratios are 1.261, 1.295 and 1.160. Its paired
median CPU increases 11.4%, while Interpreted improves with paired CPU ratio
0.957. Candidate bytecode's contemporary median is 700.607 ms CPU/query
versus Interpreted's 674.156 ms (3.9% higher). Saving 5,802 wrappers and
reducing operand source-allocation instructions from 22,183 to 16,381 does
not turn this CLP workload into a measured speedup.

Post-timing collection metadata does not support a simple explanation of
fewer collections retaining more Minesweeper bindings: measured collections
increase **88 to 91**, maximum binding count falls **1,555 to 1,540**, maximum
substitution count increases **1,224 to 1,327**, and maximum trail entries
increase **792 to 891**. Sampled heap cells fall **3,916 to 3,414**. These
different collection/store shapes are profiling leads only; measured atomic
sampling cannot establish a causal explanation or process-memory savings.

### Breadboard

| Case | Baseline bytecode CPU ms | Interpreted CPU ms | Typed bytecode CPU ms | Paired wall ratio | Paired CPU ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| RC | 5.194 | 4.688 | 4.787 | 0.969 | 0.978 |
| Divider | 6.970 | 6.513 | 6.646 | 0.983 | 0.997 |
| Transistor | 12.563 | 14.890 | 12.861 | 1.028 | 1.024 |
| Wide disconnected | 15.030 | 14.063 | 12.902 | 0.894 | 0.901 |

Wide disconnected improves in all three bytecode pairs: CPU ratios are
**0.819, 0.964 and 0.901**, with median 0.901 (9.9% less CPU); wall paired
median is 0.894. Its contemporary bytecode CPU median is 8.3% below
Interpreted, clearing this previous local breadboard regression. Wide's
post-timing probe records 105 typed attempts/wrappers avoided, with operand
source-allocation instructions falling from 334 to 229.

RC, divider and transistor have mixed paired samples. Their bytecode CPU
ratio ranges are **0.895-1.025**, **0.922-1.017** and **0.922-1.104**,
respectively, so the small median changes do not establish broad gains.
Transistor's contemporary bytecode CPU remains 13.6% below Interpreted;
RC and divider are about 2.1% and 2.0% above it. Contemporary control paired
CPU medians also vary: RC Interpreted 1.083, divider Reference 0.929, and
transistor Interpreted 0.942. These host/runtime shifts remain visible in
the raw records.

All four cases prove typed dispatch after timing. RC/divider/transistor
probes record 75/133/325 avoided wrappers, with source-allocation instructions
falling 287 to 212, 464 to 331, and 1,102 to 777. Each timed placement passes
the physical and independent optimum checks. Local control and wide
improvements are useful, but the Minesweeper regression and mixed remaining
breadboard results keep bytecode opt-in.
