# Register lifetimes and incremental body allocation - 2026-10-16

The previous head/register implementation was committed and pushed as
[`adbc6e1`](https://github.com/hyperswine/NeoProlog/commit/adbc6e1a826ef1dfea775afec17bc0f0253c909b).
Its [CI run](https://github.com/hyperswine/NeoProlog/actions/runs/38870624660)
passed both Ubuntu and macOS, including the macOS GHC SDK metadata repair and
link preflight. The changes described below follow that published snapshot.
The compiled backend remains opt-in; public solving still uses the interpreted
native backend.

## Implementation

`Compile` emits an additional flat construction plan for each body goal.
Logical locals are direct operands, rather than entries in the temporary
register array. A last-read analysis recycles scalar and constructor registers.
The VM reads every child address before overwriting a recycled destination,
including repeated operands. Scalar sharing still uses exact float bits.
The head matcher allocates only its head-prefix register array when it needs
to construct a free caller subtree.

`Bytecode.activateHead` reserves the original local-ID range, matches the head
and propagates CLP in the existing whole-head transaction. It returns a pure
body frame containing the activation base and remaining immutable code.
`materializeNext` constructs just the next reached goal. The driver installs
that goal and an optional suffix frame. Failure, errors and backtracking can
skip later body graphs without constructing or scheduling them. The final
goal removes its frame before dispatch, preserving the existing tail-return
boundary.

Every goal records its locals and a persistent suffix-live `IntSet`. Pending
frames protect those future logical IDs during collection; the current goal
protects its raw heap graph. Materialization resolves only current locals
through `Bridge.lookupVariables`, preserving raw alias identities after
relocation. Missing or stale bindings fail rather than resurrecting retired
locals. The lookup validates the environment's allocation-prefix witness even
for an empty request, and opens no transaction or import wrapper. Frozen
retries retain their matching heap and bindings. Body frames contain no heap
addresses or mutable registers, so retained or interleaved resumes remain
independent.

Normal execution performs no instruction-statistic writes. Measured execution
reports accepted-head work separately from reached body materializations,
body allocation instructions and the largest actual temporary array. Failed
head attempts remain excluded. Logical roots and heap cells are counted
separately from temporary registers.

The eager `activate` compatibility wrapper still constructs all body goals;
`instantiate` retains the original complete postorder plan for independent
checks. Clause compilation still creates that legacy plan alongside the new
plans, so cold per-query compilation and immutable code storage remain costs.
All source-local IDs are reserved up front. This slice does not implement the
full WAM argument/permanent-register environment or lazy local-root reservation.
Unsupported control/meta clauses retain their interpreted path, and table
producer heads retain their template path.

## Validation

The optimized build and all **335 Haskell properties / 23,198 cases** passed,
along with 37 LSP tests, CLI diagnostics/live-buffer/tracing/example checks and
20 benchmark-harness tests.

The new lifetime group contains 500 generated cases and seven focused checks.
Generated cases independently decode physical instructions and compare every
incremental construction/local write with legacy whole-clause rename/import
on independent thaws of one frozen heap. Comparisons include raw source IDs,
exact scalar bits, complete persistent CLP stores, bindings and dereferenced
terms. They also execute small programs through Reference and both native
backends, comparing complete raw stores. Ordinary/measured execution and
replayed frozen branches agree; ordinary counters remain zero.

Focused cases cover repeated scalars and locals, strict read-only root lookup,
dead-root retirement with future locals surviving collection, skipped 3,000-goal
bodies after failure/error/foreign cut, and earlier/future values surviving a
10,000-call helper. Retained/interleaved answers, opaque scopes, contracts,
explicit fuel and exact source traces retain parity. Compiler checks additionally
prove that a 200-level nested constructor chain uses one body temporary
register, and verify generated current/suffix local sets.

`cabal check` and `cabal sdist` pass; all 123 packaged files match the workspace
byte-for-byte. Package checking retains the existing optimization-option and
dependency-upper-bound warnings. The updated CI YAML parses successfully.

## Loaded-program measurements

Local macOS arm64, GHC 9.8.2, library and runners built with `-O2`. Each timing
row uses one checked warmup and three checked timed samples. Programs are parsed,
checked and forced outside timing. First-order and breadboard samples include
cold per-query code/cache construction, execution, full draining, projection
and validation. Distinct unused variable bases prevent sharing evaluated
searches. Measured probes run outside timing and require compiled execution.
These local reports establish no portable timing threshold.

| First-order workload | Reference median | Interpreted median | Bytecode median |
| --- | ---: | ---: | ---: |
| Helper dispatch, 10,000 iterations | 0.080009 s | 0.220584 s | 0.254488 s |
| Structured list, 300 entries | 0.129473 s | 0.378489 s | 0.353759 s |
| Structured heads, 10,000 iterations | 0.089400 s | 0.286338 s | 0.325000 s |
| Failure before 2,000 structured calls | 0.000003 s | 0.033979 s | 0.010811 s |

The early-failure probe materializes exactly one goal, with a peak of 16 active
heap cells, three tasks and one temporary register. Unreached source AST/code
still exists, and cold compilation of that large body still costs time; the
Reference resolver is substantially faster on this case. The structured-head
probe uses three temporary registers, compared with 23 in the preceding
head/register snapshot of the same fixture. The largest per-goal body plan
needs three temporaries; the structured-list probe's ten-register peak comes
from a free-head subtree, rather than its body plans.

Structured-list and early-failure samples improve over the interpreted backend,
while helper dispatch and structured heads are slower. No general throughput
gain is established. The additional per-goal dispatch/lookup and cold compiler
costs remain targets for profiling and persistent code caching.
[Raw first-order samples](../data/tsv/engine-step2-lifetimes-2026-10-16.tsv).

## Real CLP acceptance

All four breadboard cases fully drain, match exact Reference placements/order
and pass the independent physical-placement and optimum enumerator. Each
compiled probe requires positive head and body-materialization counters, so
interpreter-only fallback cannot pass. CI is configured to run these checks.

| Breadboard case | Reference median | Interpreted median | Bytecode median |
| --- | ---: | ---: | ---: |
| RC | 0.001005 s | 0.003218 s | 0.004562 s |
| Divider | 0.001755 s | 0.006015 s | 0.007682 s |
| Transistor | 0.004282 s | 0.013206 s | 0.015975 s |
| Wide disconnected | 0.010127 s | 0.014508 s | 0.015143 s |

The compiled path remains slower on these small circuits. The acceptance
establishes correctness and exercised incremental allocation, rather than a
breadboard speedup. [Raw breadboard samples](../data/tsv/engine-step2-lifetimes-breadboard-2026-10-16.tsv).

The 16x16 minefield with 50 bombs and at most two bombs in every overlapping
2x2 window also fully drains under both native backends. Exact Reference
answers/residuals and independent dimensions, binary-cell, bomb-count and all
225 window checks pass. Unlabelled setup checks shape/cell aliases and exact
Reference residuals instead of claiming a completed grid.

| Minefield phase | Reference median | Interpreted median | Bytecode median |
| --- | ---: | ---: | ---: |
| Constraint setup | 0.072304 s | 0.486629 s | 0.559259 s |
| Ordinary first grid | 0.077990 s | 0.610465 s | 0.568242 s |

Each row uses one checked warmup and three checked fresh processes. A separate
untimed compiled probe reports 8,443 accepted activations, 12,619 reached body
goals and 19,863 body allocation instructions. Its maximum temporary array has
11 registers, compared with 25 in the previous snapshot of the same workload;
the active heap peaks at 4,052 cells versus 4,464 previously. Both native
backends remain slower than Reference, and the small timing differences are
mixed. [Raw minefield samples and probe](../data/jsonl/engine-step2-lifetimes-minefield-2026-10-16.jsonl).

## Compiled residency

All 28 fresh-process compiled samples pass the existing RSS and RTS maximum-live
bound of 1.5 times the 10k/100k prefix maxima. The matrix includes repeated
million-iteration mutual recursion, live choices and `findall`, plus helpers,
structured arguments, CLP, completed tables and dynamic facts. Ordinary and
measured runs are separate; every ordinary counter remains zero.

Peak RSS ranges from 131.06 to 132.17 MiB, including process startup and source
fingerprinting. Measured active heaps peak at 1,027 cells, with at most four
tasks, two choices and three temporary registers. Larger caller-owned answers
or retained checkpoints still deliberately retain their memory.
[Raw compiled residency samples](../data/jsonl/engine-step2-lifetimes-tail-2026-10-16.jsonl).

This is bounded residency, not a lower process-RSS claim: the previous snapshot
reported roughly 126-128 MiB. The current compiler retains additional immutable
body plans, and process peaks also include runner/source metadata work.

The six-sample interpreted mutual/helper recheck also passes against the same
runtime source. Peak RSS ranges from 131.05 to 132.08 MiB, with at most 1,030
measured active heap cells and four tasks.
[Raw default-backend recheck](../data/jsonl/engine-step2-lifetimes-native-tail-2026-10-16.jsonl).

## Remaining Step 2 work

Compiled control continuations, indexing instructions, full argument/permanent
register environments, load-time caches with invalidation, determinism-directed
generation and wider acceptance remain planned. The public backend choice is
unchanged until parity and consistent throughput gains support switching it.

## Reproduce

```sh
cabal build all --offline --enable-tests --enable-benchmarks --enable-optimization=2
cabal test all --offline --enable-benchmarks --enable-optimization=2 --test-show-details=direct
"$(cabal list-bin bench:machine-bytecode --enable-optimization=2)"
"$(cabal list-bin bench:machine-breadboard --enable-optimization=2)"
"$(cabal list-bin bench:machine-minefield --enable-optimization=2)" --engine bytecode --phase ordinary --size 16 --bombs 50 --measured
python3 bench/check-tail-memory.py "$(cabal list-bin bench:machine-tail --enable-optimization=2)" --backend bytecode --output /tmp/infera-lifetime-memory.jsonl
```

Runtime-source SHA-256:
`e95dbbb215c8a4ef82c8a3afbe3e14068addd3afada4a5161481d39626ac54c9`.
Raw files preserve their own workload/dependency fingerprints and timing scope;
historical samples remain unchanged.
