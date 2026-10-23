# Step 1 follow-up and Step 2 foundation - 2026-10-16

The large ordinary-minefield regression is resolved, and the first Step 2
compiler/VM slice is implemented behind an explicit backend selection. The
public solver still uses the interpreted native machine. This first slice
establishes compiled activation and direct user-call dispatch; it does not yet
establish a bytecode throughput improvement or complete Step 2.

## Step 1 follow-up

The [previous native recheck](data/jsonl/performance-step1-2026-10-16.jsonl) timed out
while generating a 16x16 minefield with 50 bombs and at most two bombs in every
overlapping 2x2 window. Profiling isolated these costs:

* Ordinary head unification repeatedly validated the entire historical
  substitution, even when no watched constraint could propagate another write.
* Accepted native-state synchronization scanned old shared compound values and
  reconstructed whole sets of logical root IDs at each activation.
* Arithmetic normalization exported and re-imported unchanged shared grid/list
  suffixes. Protected-root deduplication also used quadratic list operations.
* Most significantly, a tabled predicate called with constrained variables
  entered the plain-clause fallback through a new table-producer driver. That
  reconstructed and validated the complete caller heap for each clause body,
  even though this call could not use a variant table.

The driver now detects the same constrained-variable condition before entering
the table boundary and runs those clauses on the active native driver. It keeps
candidate indexing, contracts, fuel, return frames and cut ownership. Actual
table producers and their cache semantics remain unchanged. Head-unification
errors retain their clause-head source location in both paths.

Native CLP synchronization now has an explicitly documented internal monotone
extension path. Actual heap writes still pass through `CLP.applyBindings` and
retain the complete resulting store. Watched writes reconcile propagated new
bindings; unwatched writes already mirror the heap. The strict arbitrary-state
`apply`, `syncBindings` and startup `syncState` paths still validate external
states. Generated tests cover sparse roots, alias representatives, metadata-only
constraint variables, propagation, rollback and immutable checkpoints.

Graph normalization memoizes existing heap addresses and shares unchanged
structures. Numeric ground expressions use the same arithmetic evaluator as the
reference; nonground or invalid expressions retain their syntax. A temporary
goal root protects an already-popped tail call while collection relocates it.
Four hundred generated normalization cases compare raw IDs, scalar bits and
idempotence with the reference transformation.

## Minefield and breadboard measurements

Local macOS arm64, GHC 9.8.2, Cabal library and runners built with `-O2`.
Each row uses one checked warmup and three checked samples. Minefield samples
use separate fresh processes; loading and parsing are outside the timer. Timing
includes solving, full draining, projection and validation. Native samples check
the exact Reference answer and residual order outside the timer. Ordinary
generation also independently checks dimensions, binary cells, bomb count and
all 225 window caps. Setup leaves cells unlabelled and checks grid/flattened-cell
shape, cell aliases and exact Reference residuals.

| Loaded-program workload | Reference median | Native median |
| --- | ---: | ---: |
| 16x16 minefield constraint setup | 0.059602 s | 0.388451 s |
| 16x16 ordinary first minefield, 50 bombs | 0.066860 s | 0.432120 s |
| Breadboard rc | 0.000843 s | 0.002594 s |
| Breadboard div | 0.001449 s | 0.005367 s |
| Breadboard tri | 0.004009 s | 0.011028 s |
| Breadboard wide disconnected | 0.008183 s | 0.010513 s |

The ordinary native minefield now completes comfortably within the previous
30-second budget. It remains about 6.5 times slower than the current Reference
in this loaded-program comparison. Breadboard checks retain exact answers,
reporting and independent optimum checks; these small cases also remain slower
on the native machine. No general throughput advantage is claimed.

Raw data: [minefield](data/jsonl/engine-step2-minefield-2026-10-16.jsonl),
[breadboard](data/tsv/engine-step2-breadboard-2026-10-16.tsv). Historical files are retained
with their original source fingerprints and timing scopes.

The [fresh CLI matrix](data/jsonl/engine-step2-cli-2026-10-16.jsonl) uses the same local
`-O2` build with one checked warmup and three checked processes, including
startup, loading and output. Reverse improves from 32.551 to 19.369 seconds,
loop from 0.752 to 0.485, untabled Fibonacci from 4.168 to 2.694 and queens
from 1.311 to 0.578. General native throughput still trails the pre-migration
baseline, whose library profile differed. The
[application recheck](data/jsonl/performance-step2-2026-10-16.jsonl) records ordinary
16x16 generation at 0.476 seconds, setup at 0.451, seeded generation at 5.844,
all-pairs closure at 0.091 and wide breadboard placement at 0.044. These CLI
timings have a different scope from the loaded-program table above.

## First Step 2 slice

[`Infera.Compile`](../src/Infera/Compile.hs) compiles supported first-order
clauses into an opaque, validated `ClauseCode`: flat postorder instructions
allocate variables, scalar constants and compounds into local registers.
Original body templates remain available for source lookup. Local variable IDs,
repeated-variable sharing, scalar types and exact float bits are preserved.
Clauses with control/meta goals, uncallable goals, malformed variable IDs or
nested body cuts retain the existing interpreter path.

[`Infera.Machine.Bytecode`](../src/Infera/Machine/Bytecode.hs) instantiates those
instructions directly on the heap. It reserves the same fresh logical IDs as
the interpreter, then executes flat instructions without traversing renamed
source `Term` trees. Activation is atomic, including allocation, interning and
logical roots. Head matching still uses the existing occurs-checked native
unifier and persistent CLP transaction.

[`Control`](../src/Infera/Machine/Control.hs) exposes `Interpreted` and `Bytecode`
through `startWithBackend`, `startMeasuredWithBackend`,
`startTracedWithBackend`, `startGoalsWithBackend` and `solveQueryWithBackend`.
Existing entry points continue to choose `Interpreted`. The compiled cache is
currently built per query/checkpoint startup, including each table-producer
startup, from the immutable program and clause ordinals. It is not yet a
load-time program cache.

General table producers still rename/import their head and body templates and
use persistent head unification at the fixedpoint boundary. Their native body
callbacks select the requested backend for subsequent predicate activations;
this slice does not compile table-producer heads.

Compiled bodies use direct tasks only for statically known ordinary user
predicates. Builtin precedence and name-wide dynamic lookup retain generic
dispatch. Direct tasks share the existing call/return, indexing, commitment,
backtracking, tail retirement, collection, tracing and frozen-checkpoint paths.
Measured execution exposes compiled-activation, instruction and direct-call
counts; ordinary solving leaves counters disabled.

| Loaded-program first-order workload | Reference | Interpreted | Bytecode |
| --- | ---: | ---: | ---: |
| Helper dispatch, 10,000 iterations | 0.049944 s | 0.140003 s | 0.143158 s |
| Structured list accumulator, 300 entries | 0.083537 s | 0.285744 s | 0.285225 s |

These medians include cold per-query cache construction and execution, with one
warmup and three samples. They show no measurable gain from this initial slice.
Independent arithmetic/list models and complete ordered Reference observations
pass. Untimed measured probes verify 20,001 / 601 compiled activations,
310,004 / 11,104 instructions and 20,000 / 600 direct calls respectively, so
success cannot be attributed to falling back entirely to the interpreter.
[Raw samples and scope](data/tsv/engine-step2-bytecode-2026-10-16.tsv).

## Native residency recheck

All 28 fresh-process checks passed the existing bound on both peak process RSS
and RTS maximum live bytes: at most 1.5 times the 10k/100k prefix maxima. The
matrix includes repeated million-iteration mutual recursion, live alternatives
and `findall`, plus helpers, structured arguments, CLP, completed tables and
dynamic facts. Ordinary execution and opt-in metric sampling are checked
separately. Peak RSS ranges from 126.98 to 128.11 MiB; measured active heaps
stay at or below 1,034 cells, with at most five tasks and two choices.

These are checks of the default interpreted native backend after the Step 1
fixes, rather than a million-iteration acceptance gate for Bytecode. Compiled
execution currently has the generated heap/snapshot/three-engine comparisons
and the smaller benchmark probes described above. Retaining previous answers
or growing live output deliberately retains caller-owned memory.
[Raw residency samples](data/jsonl/engine-step2-tail-2026-10-16.jsonl).

## Validation and CI

* `cabal build all --offline --enable-tests --enable-benchmarks --enable-optimization=2` passed.
* All 315 Haskell properties passed: 22,180 cases, including 400 generated
  compiled-versus-interpreted activation comparisons, 400 generated three-engine
  execution comparisons and the larger minefield acceptance case.
* All 37 LSP tests, CLI diagnostics/live-buffer/tracing/example acceptance and
  all 20 benchmark-harness tests passed.
* `cabal sdist` passed; 87 source, test, benchmark and documentation files were
  checked byte-for-byte against the archive. `cabal check` exited successfully
  with the existing optimization-option and dependency-upper-bound warnings.
* Compiled tests cover ordered duplicates, contracts, delayed errors, explicit
  fuel, CLP, tables, dynamic facts, generic control fallback, source traces,
  NaN payloads, signed zero, accepted aliases and retained/interleaved resumes.
  Heap tests cover stale handles, overflow rollback, snapshots and occurs checks.

The [last published CI run](https://github.com/hyperswine/NeoProlog/actions/runs/38856657248)
passed the Ubuntu job. Its macOS job failed before Infera compiled: the inherited
Command Line Tools 27 SDK exposed an `arm64e.x1` target that the GHC 9.8 linker
could not read. The workflow now selects the installed Xcode 26.6 toolchain and
SDK explicitly on `macos-26`, before setting up GHC. The
[runner image inventory](https://github.com/actions/runner-images/blob/macos-26-arm64/20261013.0424/images/macos/macos-26-arm64-Readme.md)
lists that installation. Local shell syntax checks pass; the changed hosted
workflow has not yet run. CI now also checks the large native minefield and the
validated opt-in bytecode benchmark, without timing thresholds.

## Continue Step 2

The next milestones are load-time compiled-program ownership, specialized head
matching/unification instructions, persistent argument/environment registers,
compiled control continuations and index/dispatch specialization. Each must
retain ordered parity and the established rollback/ownership/trace contracts.
Compare current-source interpreted and compiled execution before changing the
default. Full Step 2 completion remains governed by the
[roadmap](2026-10-16-ENGINE-ROADMAP.md#step-2-bytecode).

## Reproduce

```sh
cabal build all --offline --enable-tests --enable-benchmarks --enable-optimization=2
cabal test all --offline --enable-benchmarks --enable-optimization=2 --test-show-details=direct
"$(cabal list-bin bench:machine-minefield --enable-optimization=2)" --engine native --phase ordinary --size 16 --bombs 50 --timeout 30
"$(cabal list-bin bench:machine-bytecode --enable-optimization=2)"
"$(cabal list-bin bench:machine-breadboard --enable-optimization=2)"
python3 bench/check-tail-memory.py "$(cabal list-bin bench:machine-tail --enable-optimization=2)" --output /tmp/infera-tail-memory.jsonl
```

Runtime-source SHA-256 for these samples:
`33ed8df96652e94412af04f94823e3b84ec71c6a3cf6b1f73be82935e232e060`.
This hashes sorted `src/**/*.hs` paths and contents, matching the residency
runner. Individual benchmarks also record their own workload/dependency hashes.
