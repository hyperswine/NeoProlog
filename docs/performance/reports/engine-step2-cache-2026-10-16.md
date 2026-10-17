# Predicate code caching and dispatch - 2026-10-16

The compiled-control implementation was committed and pushed as
[`87d3972`](https://github.com/hyperswine/NeoProlog/commit/87d3972eb042b49dcc7bf513df4b6ed26599c12a).
This stage adds reusable source-owned clause plans and query-local predicate
routes. It removes a large program-size-dependent dispatch cost, but the
representative results still do not justify making bytecode the public
default. Bytecode remains opt-in.

## Implementation and ownership

`Pred.predClauseCache` holds an immutable source clause and a lazy
`Maybe ClauseCode` for each ordinal. Loading, inference and displaying a
predicate do not force its compiled plans. The first selected use compiles
that clause; later queries or table-producer startups using the same immutable
predicate can share the evaluated plan. Unsupported compilation results are
cached too. Plans contain source syntax and instructions, never heap handles,
mutable arrays, query substitutions, table answers or dynamic facts.

`Program.addClause` updates the affected cache entry while preserving the
other entries. Older programs and checkpoints retain their original entries.
Because `Pred` is a public record, callers can also replace `predClauses`
without updating its cache. `Compile.Cache.lookupClauseCode` therefore checks
the selected clause's exact source witness before reuse: variable count,
head, body order, constructor/scalar types and scalar values. Floating-point
identity uses bits, preserving signed zero and NaN payloads. A missing or
stale witness compiles the actual clause instead. The machine memoizes the
selected result once per query, including `Nothing`, avoiding repeated source
comparisons on recursive calls.

Direct edits still carry the existing responsibility to maintain indexes and
inference metadata when heads or declarations change. The source witness
protects compiled plans; it does not repair those independent program fields.
For a valid direct clause edit, rebuilding `predClauseCache` with
`buildClauseCache` restores cross-query reuse; a stale entry otherwise compiles
the replacement once in each query.

Source plans do not embed determinism, sort, mode, purity, indexing or table
decisions. Query startup builds routes from the exact current `Program`,
including its predicate definitions, builtin precedence, name-wide dynamic
flags, indexing/tabling flags and tail-eligibility proofs. Thus declaration,
inference and flag changes use current runtime metadata even when clause
syntax is unchanged. A retained checkpoint continues to use its own program
and routes.

Previously, every ordinary compiled call classified its name with
`nameHasFlag`, which could scan every predicate, then looked up the predicate;
`DirectRun` repeated the lookup. Startup now builds the dynamic-name set and
route map once. `DirectRun` carries its selected route and definition through
the existing contract, table, fuel and return logic. Invocation/data graphs
and strict logical-root lookup retain their previous behavior.

The query-local clause memo also survives retries and opaque returns. Its map
spine is strict at the `Running` boundary, preventing a delayed child-field
selector from retaining a completed child driver; code values remain lazy.
Every query still receives a fresh heap and complete solver state.

Measured execution exposes three distinct counters:

- `code_cache_hits`: reuse of the query-local selected-clause memo.
- `predicate_cache_hits`: the immutable predicate entry's source witness
  matched. This does **not** mean an earlier query had evaluated its plan.
- `predicate_cache_misses`: a missing or stale witness required compilation
  from the current source.

Normal execution keeps these counters at zero. The post-timing helper probe
records 19,998 query-local hits, three matching predicate witnesses and zero
misses, with 20,001 accepted compiled activations. Padding the program with
unused predicates leaves these counts unchanged.

## Validation status

The optimized Haskell suite passed **353 properties / 24,412 cases**. All 37
LSP tests, CLI diagnostics/live-buffer/tracing/example checks and 20
benchmark-harness tests passed.

The completed cache matrix contains 216 checked process records. All nine
broader warm [first-order/control fixtures](../data/tsv/engine-step2-cache-bytecode-2026-10-16.tsv)
and four [breadboard cases](../data/tsv/engine-step2-cache-breadboard-2026-10-16.tsv) also
passed with positive compiled probes. Breadboard placements match Reference
and pass the independent physical/optimum validators. All 30 fresh-process
samples in the full [compiled residency gate](../data/jsonl/engine-step2-cache-tail-2026-10-16.jsonl)
passed. Peak RSS spans 145.44-149.30 MiB; measured active heaps stay at or below
1,027 cells, with at most four tasks, two choices, two scopes, three cut owners
and three temporary registers. This is bounded live state, not a process-memory
reduction: the previous control report recorded 139.38-142.42 MiB RSS.
The new compiled-control million-call sample retains its selected arm and
opaque parent with 1,025 active cells and one temporary register. It records
999,999 query-local memo hits, three source-witness hits and zero misses.
Every normal sample keeps all 26 counters at zero. All six samples in the
[interpreted residency recheck](../data/jsonl/engine-step2-cache-native-tail-2026-10-16.jsonl)
also pass, with 147.20-148.27 MiB peak RSS and at most 1,030 active heap cells.
The runtime source hash remains unchanged throughout all measurements.

`cabal check` and `cabal sdist` pass. The source package includes the cache
module, generated tests, new runner and all six new report/data files. Package
checking retains the existing optimization-option and dependency-upper-bound
warnings. CI now checks cold and warm compiled helper/control queries on both
configured platforms; these new changes have only been validated locally so
far and remain uncommitted.

## Matched baseline and measurement scope

The [raw matrix](../data/jsonl/engine-step2-cache-2026-10-16.jsonl) compares the published
control core with this implementation on local macOS arm64, GHC 9.8.2,
library and runners built with `-O2`. The baseline's 26 `src` files were
checked against the Git blob IDs from `87d3972`: every file matched, with no
changed or extra source files. Its new `machine-cache` runner differs from
the current runner only by removing the three unavailable cache counter
assertions and fields. Workloads, queries, forcing, timers, independent
models, Reference comparisons and post-timing compiled/control probes are
otherwise identical.

Six cases run under Reference, interpreted native and bytecode. The baseline
has cold rows; the new implementation has cold and warm rows. Each of these
54 groups contains one discarded fresh-process warmup and three measured
fresh-process samples: **216 records, 162 timed samples**. A discarded process
can warm host/code pages, but cannot warm the next process's program cache.

Each runner parses/checks its program and forces source/runtime metadata
outside timing without inspecting the compiler cache. It also computes and
validates its Reference oracle before timing. A cold native/bytecode row is
the first such solver invocation in that process, with no compiled preprobe.
A warm row first drains and validates one query outside timing, then executes
a distinct query with a different unused variable base. Only immutable
program plans are shared; heap, store, tables and dynamic state are fresh.
The timed region includes query startup, any reached compilation, execution,
full draining, projection and validation. Loading and CLI startup are excluded.
Bytecode's measured cache/path probe runs only **after** the timed query.

Here, cold/warm describes native clause-code preparation, not a first-ever
Reference execution: every process has already run its Reference oracle.
Warm queries also differ in normal CPU/runtime/GC warmth, so their difference
from cold queries is not an isolated measurement of compiler cost.

## Results

Wall medians in seconds; each column's phase is explicit. All rows match the
complete Reference answer/residual/output/error stream and an independent
integer or grid model.

| Case | Baseline bytecode cold | Current Reference cold | Current interpreted cold | Current bytecode cold | Current bytecode warm |
| --- | ---: | ---: | ---: | ---: | ---: |
| Helper, 10,000 iterations, no padding | 0.274562 | 0.068546 | 0.303210 | 0.243945 | 0.278023 |
| Helper plus 100 unused predicates | 0.726704 | 0.073762 | 0.230110 | 0.259678 | 0.293552 |
| Helper plus 1,000 unused predicates | 8.835585 | 0.071713 | 0.233117 | 0.239413 | 0.249105 |
| Structured heads, 10,000 iterations | 0.400171 | 0.094654 | 0.317494 | 0.351459 | 0.281274 |
| Once/not/if, 300 iterations | 0.015649 | 0.001253 | 0.011749 | 0.016821 | 0.011624 |
| First 16x16 minefield grid, 50 bombs | 0.679470 | 0.108857 | 0.679388 | 0.688116 | 0.594498 |

The 1,000-predicate helper improves from 8.835585 s to 0.239413 s, a **36.9x
local median improvement**, or 97.3% less wall time. The baseline's no-padding
to 1,000-padding median grows 32.2x; the new cold medians stay near 0.24 s.
This is evidence for removing repeated whole-program dispatch scans, rather
than a general inference-throughput multiplier. That padded workload has the
same source/query fingerprint `35c7ee962aa4a0b5a06b47ee77238898` in both stages,
and all engines/phases retain answer fingerprint
`bbc6827afd2080d40cb27e3595cf8b1b` for the independently checked sum 50,005,000.
All six workload fingerprints and their answer fingerprints agree across the
matrix.

The smaller cold helper and structured-head medians improve 11.2% and 12.2%
against the matched bytecode baseline. Cold controls are 7.5% slower, and the
minefield difference is 1.3%. Against the current interpreted backend, cold
bytecode structured heads are **10.7% slower** and controls **43.2% slower**.
Reference remains faster on every displayed case.

Warm results are mixed. Structured heads, controls and minefield have lower
warm bytecode medians, while all three helper variants have higher warm
medians. The warm Reference and interpreted rows are also preserved in the
raw file; a warm bytecode column must not be compared with a cold interpreted
column as if the phases were identical.

Sample ranges make the limits visible. The padded helper's baseline spans
7.931380-8.921510 s and new cold samples span 0.235238-0.245114 s, supporting
the large scaling result. Structured-head warm bytecode spans
0.273536-0.469976 s; minefield baseline bytecode spans
0.655728-1.050768 s. Baseline and current stages ran in serial blocks, rather
than randomized/interleaved controlled-runner trials. CPU samples and all wall
samples remain in the raw matrix. Smaller changes and warm/cold differences
must be interpreted with that variation and stage ordering in mind.

The minefield case fully drains its `once` continuation and checks one ground
16x16 binary grid, exactly 50 bombs and all 225 overlapping 2x2 windows having
at most two bombs. Its post-timing compiled probe has 8,763 accepted
activations, 1,089 compiled control instructions, 8,796 query-local code hits,
31 matching predicate witnesses and zero misses. This confirms execution of
the compiled/cache paths without putting instrumentation in the timing rows.

The separate warm breadboard comparison also limits the default conclusion.
Transistor bytecode is 0.022791 s versus interpreted 0.014997 s, about 52%
slower. Wide disconnected is 0.019656 s versus 0.019810 s, effectively tied
within the visible sample variation. Correct placements and optima establish
acceptance; they do not establish a consistent breadboard speedup.

## Default migration and remaining work

The dispatch scaling defect is repaired, and source plans can now survive
across queries on an unchanged immutable program. Reached invocation/data
materialization, raw export/normalization, local-operand dispatch, indexing
instructions and the full argument/permanent-register environment remain
performance targets. Representative regressions and mixed warm results keep
the [default migration gates](../../engine/roadmap.md#making-bytecode-the-public-default)
open. Bytecode remains opt-in until complete parity, cross-platform CI,
real CLP acceptance, retained-checkpoint/residency checks and checked cold/warm
performance support switching the facade. Explicit interpreted selection and
the Reference oracle remain available.

## Reproduce

Build with library and runner optimization enabled, then launch each sample
as a separate process. Warm performs its own checked pre-query; cold does not.

```sh
cabal build bench:machine-cache --offline --enable-benchmarks --enable-optimization=2
"$(cabal list-bin bench:machine-cache --enable-optimization=2)" --engine bytecode --phase cold --case helper-1000
"$(cabal list-bin bench:machine-cache --enable-optimization=2)" --engine bytecode --phase warm --case helper-1000
"$(cabal list-bin bench:machine-cache --enable-optimization=2)" --engine bytecode --phase cold --case minefield-16
```

Runtime source SHA-256 values recorded in the matrix:

- Published control baseline:
  `20348e7e06deb452216945db5fb38f9c38e5f6381017f0cd01ab66d6fd7434c1`.
- Predicate-cache implementation:
  `5ab0407026c7cd5fb445007188be0765ed37eb21f3fe4d3576e1b5f1e72ecdd1`.

The corresponding runner/runtime source fingerprints are
`023f33ee94d0424e04cd4bf208ff9074` and
`08a1268400e8e8fd0017e54ab5e965aa`. Historical reports and their samples remain
unchanged; the existing multi-case bytecode/breadboard runners now explicitly
label timings after their untimed compiled probe as warm reached predicate
plans.
