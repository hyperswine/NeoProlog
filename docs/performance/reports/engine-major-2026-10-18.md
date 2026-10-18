# Four Core designs - first implementation and measurements

Date: 2026-10-18

The first implementations deliver large gains where repeated clause probing
or full table rounds dominate: nested dispatch is **7.16x faster** and the
240-node table closure is **23.48x faster** in this checked local matrix.
Leading integer guards improve by about 15%. Precise collection reclaims dead
activation cells. Breadboard and Minesweeper remain near their earlier times;
these changes do not establish a general throughput improvement. Several
ordinary workloads still take 2-6% more CPU.

The [design document](../../engine/major-design-2026-10-18.md) describes native
constraint posting/search, bounded compiled decisions, precise activation
liveness and delta tabling. All four run in the existing public Core.
Constraint propagation still uses the persistent kernel. Mutable trailed
domains and general dependency-driven table scheduling remain future work.

## Reproduction and identities

The baseline is an archive of `7278385`. Its only copied working-tree example
change is the user's existing comment in `examples/v2_decls.nprolog`, preserved
unchanged in both checkouts. The candidate is that revision plus this working
tree's implementation. Both builds use GHC 9.8.2 on the same macOS arm64 host,
with **-O2 for library and benchmark**. These are different optimization settings
from some older reports, so those older absolute times are not a controlled
baseline for this change.

| Identity | Baseline | Candidate |
| --- | --- | --- |
| Runtime SHA-256 | `4702b3dbaaf54207ddb91c171d6149eda4ecbc0ce5231072f3cfff1e9a1b54de` | `9bef044add851817feea6b44c3c53094446391ddb4def613f41b48b69d8ef549` |
| Runner binary SHA-256 | `a67f6325de6d6245d800d043129ed6340709b7739f65da96fa8eb1c9fb337b22` | `6f889bc8faacacbf32e9189e08f15c946ba257bdb41120bc48ad50da41cd6d5f` |

The identical runner source SHA-256 is
`69ffc4581194c5969a7a7072936c5528ac63f60573ddfaa10b0366c4485ba4b8`.
Runtime hashing sorts all `src/**/*.hs` paths and hashes each relative path,
NUL, file bytes and NUL. Raw rows also carry workload fingerprints, batch
sizes, round/order, platform, command and UTC start time. Source, binary and
runner hashes were checked again after each measurement matrix.

Build the same `bench/core-major.hs` and Cabal component in both checkouts:

```sh
cabal build exe:infera bench:core-major --offline --enable-optimization=2
cabal list-bin bench:core-major --enable-optimization=2
# Run the returned executable from its checkout, for example:
/path/to/core-major --case table-cycle240 --batch 12 --timeout 60 +RTS -T -RTS
```

## Loaded-program method

[Final raw data](../data/jsonl/engine-major-2026-10-18.jsonl) contains one checked
fresh-process validation sample per case/version, then five measured pairs.
Order alternates baseline/candidate each round. Batches target about 0.25 s of
baseline query CPU using the validation sample, capped at 2,000 queries.
Builds, tests, profiles and other benchmark processes ran sequentially.

Every process parses/infers the program, fully drains a Reference oracle and
checks its independent model before the clock. A separate Core-only preflight
fully drains the query and rejects fallback. Each timed invocation constructs
fresh query state through a NOINLINE boundary and a varying unused-root count;
no solved state or answer stream is reused. The timed region includes per-query
Core compilation, execution, answer projection and validation against the
complete ordered oracle. Parsing, inference, source fingerprinting, the oracle
and preflight are excluded. Errors, output, residuals and exhaustion would fail
these ground benchmark cases.

Models check scalar results, reversal, queen conflicts, exact ordered ring
closure, and every overlapping 2x2 Minesweeper window plus its total 50 bombs.
Breadboard checks independently validate hole collisions, shorts, node/hole
arithmetic, score and optimum over the fixed placement window. Its optimum
model takes component net pairs/rows and the selected wired nets from the
Reference answer, so that independent optimum is conditional on those circuit
fields. Exact full-stream parity separately checks the candidate's component
and placement terms against Reference.

RTS allocation deltas include final sampling/GC bookkeeping, with that final
forced GC outside CPU/wall timing. Process maximum live bytes include setup,
Reference and preflight; they are **not** an isolated Core live-heap/RSS measure.

## Results

Median CPU milliseconds per fresh query. Speedup is baseline divided by
candidate; below 1.00x is slower. Allocation change is candidate relative to
baseline. Individual wall/CPU samples and GC counters remain in the raw data.

| Case | Before ms | After ms | Speedup | GHC allocation |
| --- | ---: | ---: | ---: | ---: |
| `controls` | 0.137 | 0.137 | 1.00x | +0.0% |
| `guards` | 2.330 | 2.031 | 1.15x | -4.1% |
| `deep-index` | 34.471 | 4.815 | 7.16x | -72.7% |
| `liveness` | 12.944 | 13.075 | 0.99x | -0.7% |
| `table-cycle` | 0.138 | 0.056 | 2.47x | -7.8% |
| `table-cycle240` | 22.281 | 0.949 | 23.48x | -91.5% |
| `core-nrev` | 7.990 | 8.371 | 0.95x | +1.5% |
| `core-loop` | 9.517 | 10.044 | 0.95x | -0.1% |
| `core-fib` | 41.977 | 42.855 | 0.98x | -9.3% |
| `core-queens` | 8.575 | 8.972 | 0.96x | +3.2% |
| `breadboard-rc` | 1.492 | 1.526 | 0.98x | +1.7% |
| `breadboard-div` | 1.847 | 1.883 | 0.98x | +1.9% |
| `breadboard-tri` | 3.757 | 3.772 | 1.00x | +1.3% |
| `breadboard-wide` | 9.069 | 9.533 | 0.95x | +4.8% |
| `minefield-16` | 33.425 | 33.411 | 1.00x | +1.1% |

Nested dispatch uses 128 clauses differentiated by nested constructors and a
second argument. Guard dispatch uses 5,000 calls with complementary integer
guards. The table cases enumerate an entire 16- or 240-node directed ring,
including the starting node through the cycle. Their `table` declaration adds
no determinism contract, so the source satisfies the delta proof; the recursive
clause is same-variant and first in its body, followed by an acyclic edge fact.
These are targeted examples, not a general 7x or 23x language speedup.

The ordinary controls sample is effectively unchanged. Reverse, loop, fib,
queens and wide breadboard retain small regressions. RC/divider/tri breadboards
and 16x16 Minesweeper are close to baseline. Native search removes the Reference
search adapter but still pays persistent propagation and heap/store
synchronization; no significant general CLP speedup is demonstrated.

### Retention evidence

`CoreLivenessTest` directly drains the native engine and asserts that collection
occurs, reclaims more than `3*N` cells for dead lists of size 100 and 300, and
retains fewer than 64 cells at its last collection. Both cases finish with
three live Core cells in the counter probe. A separate longer-spin pressure
probe records collection for larger input as well:

[Raw pressure counters](../data/jsonl/engine-major-liveness-2026-10-18.jsonl), using an initial collection threshold of one cell (adapted by the collector), with 90,000 spin calls:

| List cells | Collections | Last live Core cells | Reclaimed cells |
| ---: | ---: | ---: | ---: |
| 100 | 334 | 3 | 270,352 |
| 300 | 110 | 3 | 271,155 |
| 20,000 | 10 | 3 | 277,550 |

These counters describe logical cells after the last collection, not allocated
array capacity or process resident memory. A short run can finish before the
next collection: the initial 20,000-element probe with only 4,000 spin calls had
its last GC while the list was still needed. The longer-spin probe explicitly
continues allocation after the list becomes dead. The loaded `liveness` timing
uses 20,000 elements and 90,000 spin calls; CPU is approximately unchanged.

### Diagnosis and rejected intermediate costs

The [initial matrix](../data/jsonl/engine-major-initial-2026-10-18.jsonl) showed a
25% loop regression. Selection was refining a pure singleton even though head
and body execution already decided it. A
[second matrix](../data/jsonl/engine-major-singleton-2026-10-18.jsonl) stopped that
work, but exposed about 40 unnecessary bytes per loop call: a temporary Maybe
and a rebuilt singleton list. Returning the cached immediate-key list directly
removed that allocation. Variable-only deep paths and single-clause deep
metadata are also omitted. Intermediate rows have their own source/binary
hashes and are excluded from the final table.

The separate [baseline cost-centre profiles](../data/jsonl/engine-major-profile-2026-10-18.jsonl)
are coarse whole-process diagnostics, including loading/oracle/preflight, and
are excluded from performance ratios. In the minefield profile, bounds
propagation, normalization, registration and store synchronization remain
material costs. This supports profiling a mutable propagation/synchronization
redesign next; it does not attribute the entire timed solve to one function.

## External CLI check

Five checked fresh-process CLI samples per engine/case, after one checked
warmup, include startup, parsing/loading, solving and output. Infera uses RTS
`-N1`. Installed comparisons are SWI-Prolog version 10.0.2 for fat-darwin,
and cargo:0.10.0. [Raw CLI samples](../data/jsonl/engine-major-cli-2026-10-18.jsonl)
retain engine versions and binary hashes. This separate sequence uses fixed
engine order within each case, so it is a local comparison with startup costs,
not the alternating loaded-program matrix above.

| Workload | Infera s | SWI s | Scryer s |
| --- | ---: | ---: | ---: |
| nrev | 0.2725 | 0.0477 | 0.1353 |
| loop | 0.0192 | 0.0157 | 0.0539 |
| fib | 0.0586 | 0.0437 | 0.0745 |
| queens | 0.0268 | 0.0163 | 0.0521 |

Loop, fib and queens are within 2x SWI in this small CLI matrix; reverse is
2.01x Scryer, just over a strict 2x boundary. This is close to the requested
roughly-2x target for these four checked cases. It does not establish that
constraint-heavy, larger, mutually recursive or long-running applications meet
that target. Short cases include substantial process/loading cost.


## Correctness and packaging

- Full Haskell suite: **418 properties, 27,061 cases**, all 42 groups pass on
  the final build.
- Forced-collection sweep: **377 shipped-example and parity queries**, all
  agree with Reference and the existing machine; no skips or fallback.
- CLI diagnostics/live-buffer/trace/shipped-example/DCG/module acceptance passes.
- Editor suite: **61/61**, including the actual compiler, passes.
- Python benchmark harness tests: **34/34** pass.
- All 30 final validation samples and 150 measured processes fully drain and
  pass oracle/model checks. No timeout/failure is assigned a timing.
- New native tests compare generated labeling, minima, guarded/nested decisions,
  sparse activations and graph closures with ordered unpruned/full execution;
  error/output/residual and fresh-ID cases are also retained.
- Packaging checks: `cabal check` exits 0 with the existing optimization/dependency-bound
  warnings. `cabal sdist` and byte-for-byte archive verification pass, including
  the new Core modules, tests/fixtures, runner, design/report and raw data.


Tests exposed and fixed three existing minimum-result problems alongside the
new search driver: the winner's fresh-variable counter was lost; separately
copied roots could incorrectly share a fresh variable; and escaped constrained
locals could lose their physical watch mapping. Regression fixtures cover
aliases, distinct variables, later allocation, residual domains, invalid later
bindings and retry after failure. An independent read-only review found no
actionable correctness issue in the final source; that is additional review,
not a replacement for execution tests.

Editor validation also repaired two pre-existing test defects: a hardcoded old
extension version, and a fake-checker logging race that could close a dependency
before its result was cached. The latter now waits for publication of the exact
source/buffer snapshot. No editor product code was changed.

## Remaining priorities

1. Profile and replace the expensive persistent propagation/synchronization
   boundary with trailed mutable domains/change tracking, retaining the new
   generated/native oracles. This is the largest unfinished portion of CLP.
2. Move reusable compilation/planning to an explicit loaded-program lifetime;
   current measurements still include per-query plan/index construction.
3. Extend delta eligibility and then dependency scheduling beyond this narrow
   linear recursion proof, with ordering/limit behavior kept explicit.
4. Use slot liveness before collection to reduce allocation, and measure physical
   residency separately from logical live cells.

These first stages leave substantial design work. The data supports the targeted
clause/table wins and the retention contract, while keeping general execution
and CLP costs visible.
