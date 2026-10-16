# Compiled controls and cut barriers - 2026-10-16

The register-lifetime implementation was committed and pushed as
[`c1ea561`](https://github.com/hyperswine/NeoProlog/commit/c1ea56179be48d37ab22e999e34cedca803e200f).
Its [CI run](https://github.com/hyperswine/NeoProlog/actions/runs/38876727873)
passed. The changes below follow that published snapshot. Bytecode remains
opt-in, with an explicit roadmap to make it the public default after the
remaining correctness and performance gates pass.

## Implementation

`Compile` now emits pure control nodes for conjunction, disjunction, cuts,
`call`, `once`, negation, if-then-else and `findall`. Invocation leaves and data
operands have flat allocation plans. Control nodes retain source templates and
logical-variable sets without mutable registers or heap addresses. Binary
comma nodes remain distinct, preserving their observable trace events.

`Control` schedules conjunction children directly. Disjunction freezes the
native branch and parks its right code continuation in the existing choice
stack. Opaque searches launch code through the existing scope driver and keep
its issue/output policies. If scopes retain pure code for their selected arm;
`findall` materializes its template and target operands while its search stays
code. `call` materializes callable/argument operands and reuses native shallow
callable expansion. No auxiliary predicate activation changes fresh IDs,
fuel, contracts or trace frames.

Only reached invocation/data plans construct graphs. Untaken arms and core
control wrappers stay unallocated. Pending code, selected-arm continuations
and body suffixes contribute logical roots during collection. Frozen choices
retain matching heap/binding snapshots. The final code task leaves the native
return boundary exposed for tail reuse. Ordinary top-level invocation plans
are shared with their legacy decoder view; full control-wrapper compatibility
plans are built lazily only when those oracle APIs request them.

Compiled and interpreted cuts use one shared local/deferred-foreign helper.
A foreign marker still travels after the continuation and can be discarded by
a later local cut or a successful checked commitment. Opaque scopes retain
their isolation. Bare body cuts rewrite recursively, even inside ordinary
data, using `PutOwner`/`GoalOwner` operands for the activation base; head cuts
stay literal. Explicit `$cut` variable owners remain raw variables, and a
variable bound to `->` retains ordinary disjunction behavior. Trace mode
reconstructs renamed source syntax only for events and inherits native source
locations for nested nodes.

Normal execution writes no instruction counters. Measured execution adds
`compiled_control_instructions` and `compiled_cuts`, separate from accepted
head work and reached invocation/data allocation. Positive control/cut probes
prevent generic interpreted fallback from satisfying compiled acceptance.

Malformed local IDs or uncallable heads still reject compilation. Dynamic or
noncallable leaves and malformed control arities compile as invocation plans
whose native checks decide their behavior. Less-common meta/DCG operations
(`forall`, `minimize`, `phrase`, `emit`, file phrases) and dynamically expanded
call targets retain native dispatch. Table producer heads keep their template
path. Code caches remain per query/producer startup.

## Validation

The optimized full Haskell suite passes **344 properties / 23,805 cases**.
All 37 LSP tests, CLI diagnostics/live-buffer/tracing/example checks and 20
benchmark-harness tests also pass.
The new control group contains 300 closed search trees checked against an
independent ordered-result model, 300 mixed controls/cuts/errors/CLP/table/
dynamic cases checked against both older engines, and seven focused checks.
Small generated cases compare complete raw stores and metadata. Fuel and
source-trace comparisons include nested opaque scopes, unknown/arithmetic
errors, duplicate answers, local and foreign markers and replayed snapshots.

Focused checks cover raw if/cut/call quirks, recursive cuts inside data,
errors before first success, negation suppression, findall's first-error and
output/sharing behavior, output checks before commitment, required-success
guards, large untaken arms, future locals surviving collection and interleaved
resumes. A long helper also preserves the last-goal tail boundary. Existing
compiler and lifetime generators now include bare cuts inside data, checking
both normal and compatibility construction plans.

`cabal check` and `cabal sdist` pass. All 130 packaged files match the workspace
byte-for-byte. Package checking retains the existing optimization-option and
dependency-upper-bound warnings.

## Serial measurements

Local macOS arm64, GHC 9.8.2, library and runners built with `-O2`. Each row
uses one checked warmup and three checked timed samples. Parsing/checking is
outside timing; cold per-query compilation, execution, full draining,
projection and validation are inside. Distinct unused variable bases prevent
sharing evaluated searches. Untimed probes require positive compiled counters.
These are local reports with visible sample variation, not controlled-runner
thresholds or a general performance claim.

| Workload | Reference median | Interpreted median | Bytecode median |
| --- | ---: | ---: | ---: |
| Helper dispatch, 10,000 iterations | 0.127054 s | 0.259598 s | 0.286287 s |
| Structured list, 300 entries | 0.135972 s | 0.359522 s | 0.357093 s |
| Structured heads, 10,000 iterations | 0.091277 s | 0.270273 s | 0.357695 s |
| Failure before 2,000 calls | 0.000004 s | 0.030391 s | 0.010606 s |
| Ordered disjunction | 0.000006 s | 0.000024 s | 0.000028 s |
| Once/not/if, 300 iterations | 0.001151 s | 0.009300 s | 0.011930 s |
| Findall triplets, 100 lists | 0.000567 s | 0.004215 s | 0.003943 s |
| Cut loop, 1,000 iterations | 0.004771 s | 0.042724 s | 0.046546 s |
| Untaken 2,000-call else arm | 0.000003 s | 0.060571 s | 0.022152 s |

The untaken-arm probe executes one compiled if instruction and materializes
two invocation leaves. It peaks at 13 heap cells, two tasks and one temporary
register, with three body allocation instructions. The unchosen source/code
still exists, and compiling that large body still costs time; Reference's lazy
resolver is much faster here. Normal execution's largest body leaf/data plan
needs three registers, while the unused compatibility wrapper plan would need
2,003. The cut probe executes 1,000 compiled cuts and 2,000 control instructions.
Exact independent sums, list contents, ordered alternatives and complete
Reference search streams pass for every case.

Large skipped bodies improve over interpreted native execution, while several
small hot loops remain slower. Structured-list and findall differences are
small in these samples. Throughput remains mixed, so default migration gates
are not yet met. [Raw first-order/control samples](engine-step2-control-2026-10-16.tsv).

## Real CLP acceptance

All four breadboard cases fully drain, match exact Reference placements/order
and pass the independent physical-placement and optimum enumerator. Compiled
probes require accepted head and reached-body counters; the new control
benchmark separately proves direct control execution.

| Breadboard case | Reference median | Interpreted median | Bytecode median |
| --- | ---: | ---: | ---: |
| RC | 0.000994 s | 0.003222 s | 0.005275 s |
| Divider | 0.001597 s | 0.005289 s | 0.007937 s |
| Transistor | 0.003907 s | 0.012900 s | 0.014823 s |
| Wide disconnected | 0.010449 s | 0.013450 s | 0.015470 s |

The compiled path remains slower on these small circuits.
[Raw breadboard samples](engine-step2-control-breadboard-2026-10-16.tsv).

The 16x16 minefield with 50 bombs and at most two bombs in every overlapping
2x2 window also passes. Searches fully drain, match exact Reference answers
and residuals, and satisfy independent dimensions, binary cells, bomb total
and all 225 window caps. Unlabelled setup checks shape/cell aliases and exact
Reference residuals rather than claiming a completed grid.

| Minefield phase | Reference median | Interpreted median | Bytecode median |
| --- | ---: | ---: | ---: |
| Constraint setup | 0.072368 s | 0.510080 s | 0.575566 s |
| Ordinary first grid | 0.088487 s | 0.537230 s | 0.625076 s |

Each row uses one checked warmup and three checked fresh processes. An untimed
compiled probe reports 8,763 accepted activations, 1,089 compiled control
instructions and 14,604 reached invocation leaves. The verified grid's
fingerprint is unchanged. Its active heap peaks at 3,907 cells and its largest
temporary array has 11 registers. Both native backends remain slower than
Reference, and bytecode is slower than interpreted in these samples.
[Raw minefield samples and probe](engine-step2-control-minefield-2026-10-16.jsonl).

## Residency

All 30 fresh-process compiled samples pass the existing RSS and RTS maximum-live
bound of 1.5 times the 10k/100k prefix maxima. The historical 28-case matrix
still covers repeated million-iteration mutual recursion, live alternatives,
`findall`, helpers, structured arguments, CLP, completed tables and dynamic
facts. Two new samples hold compiled if/once continuations across a million-call
helper, retaining both an earlier shared value and a future result local.
The bytecode quick CI matrix includes these additional samples too.

Peak process RSS ranges from 139.38 to 142.42 MiB, including startup and source
fingerprinting. Absolute process peaks increased from the preceding snapshot's
131-132 MiB range. Active machine state remains bounded: measured heaps peak
at 1,027 cells, with at most four tasks, two choices, two opaque scopes and three
temporary registers. Every ordinary-mode counter remains zero.

The new compiled-continuation sample verifies one million tail transfers,
11,857 collections and two compiled control instructions, with three tasks,
two scopes, 1,025 heap cells and one temporary register. Its normal and measured
fresh processes both satisfy the residency policy. Caller-owned growing
answers and retained checkpoints retain their intended memory.
[Raw compiled residency samples](engine-step2-control-tail-2026-10-16.jsonl).

The six-sample interpreted mutual/helper recheck passes against the same
runtime source. Its measured active heaps remain at or below 1,030 cells,
with at most four tasks and one choice.
[Raw default-backend recheck](engine-step2-control-native-tail-2026-10-16.jsonl).

## Default migration

Bytecode is the intended eventual default. The next performance work is to
profile reached invocation/operand dispatch and remove repeated cold query
compilation with immutable predicate caches and correct edit invalidation.
Indexing and the full argument/permanent-register environment remain planned.
Native CLP, table and dynamic services can stay shared behind instructions.

Before switching the public facade, require complete generated/API/stdlib
and trace parity, cross-platform CI, independent breadboard/minefield
acceptance, retained-checkpoint and million-iteration residency checks, and
checked serial cold/warm timings without material representative regressions.
The switch must retain explicit interpreted selection and rerun the
default-facing CLI/editor suite. Reference remains an oracle through the
planned parity release.

## Reproduce

```sh
cabal build all --offline --enable-tests --enable-benchmarks --enable-optimization=2
cabal test all --offline --enable-benchmarks --enable-optimization=2 --test-show-details=direct
"$(cabal list-bin bench:machine-bytecode --enable-optimization=2)"
"$(cabal list-bin bench:machine-breadboard --enable-optimization=2)"
"$(cabal list-bin bench:machine-minefield --enable-optimization=2)" --engine bytecode --phase ordinary --size 16 --bombs 50 --measured
python3 bench/check-tail-memory.py "$(cabal list-bin bench:machine-tail --enable-optimization=2)" --backend bytecode --output /tmp/infera-control-memory.jsonl
```

Runtime-source SHA-256:
`20348e7e06deb452216945db5fb38f9c38e5f6381017f0cd01ab66d6fd7434c1`.
Raw files retain their own workload/dependency fingerprints and timing scopes;
earlier published samples remain unchanged.
