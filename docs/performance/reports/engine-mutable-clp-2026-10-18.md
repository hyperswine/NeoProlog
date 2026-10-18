# Mutable CLP propagation - implementation and measurements

Date: 2026-10-18

The mutable kernel reduces the checked 16x16 Minesweeper query from **33.7 ms
to 22.3 ms**, with **39.4% less GHC allocation**. Breadboard remains correct
and allocates 2-14% less, but takes **7-13% more CPU**. This is a useful linear
constraint improvement with an explicit regression on mixed/global constraint
workloads, rather than a general CLP throughput win.

The [design document](../../engine/mutable-clp-2026-10-18.md) describes sparse
mutable variable/constraint cells, native linear propagation and scheduling,
undo marks in Core choices, incremental immutable snapshots and heap binding
deltas. Absolute values, reification, all-different and general disequality
still use the persistent single-constraint reducers behind a mutable scheduler.
Their algorithms and the labeling/search policies are unchanged.

## Source and measurement method

The baseline is the committed and pushed `d20ab4a` with its preserved optimized
executables. The candidate is that revision plus this working tree's mutable
CLP changes. Both use GHC 9.8.2 on the same macOS arm64 host, **-O2 for library
and runner**, one capability and RTS allocation counters. Neither binary was
rebuilt during its measurement matrix.

| Identity | Baseline | Candidate |
| --- | --- | --- |
| Runtime SHA-256 | `9bef044add851817feea6b44c3c53094446391ddb4def613f41b48b69d8ef549` | `47864b82eefdb35382e8de1913cfdbdf733db5b2cd2d4106825a6399ee6ad405` |
| Runner binary SHA-256 | `6f889bc8faacacbf32e9189e08f15c946ba257bdb41120bc48ad50da41cd6d5f` | `795089937a30a866b9cd5d0e11fee14c671993e618a1e73a52b198c0033beac6` |

The identical `bench/core-major.hs` source hash is
`69ffc4581194c5969a7a7072936c5528ac63f60573ddfaa10b0366c4485ba4b8`.
Runtime hashing sorts `src/**/*.hs`, hashing each repository-relative path,
NUL, file bytes and NUL. Hashes were checked again after the matrix. Raw rows
also retain workload fingerprints, host, command, batch, round, order and UTC
time. Builds, tests, diagnostic probes and timings ran sequentially.

[Final raw data](../data/jsonl/engine-mutable-clp-2026-10-18.jsonl) contains
180 successful rows: one validation pair per case, then five measured pairs.
Baseline/candidate order alternates by round. Batches target 0.25 s of baseline
query CPU, capped at 2,000 queries. Each process fully drains and checks a
Reference oracle against an independent model, then runs a separate Core-only
preflight that rejects fallback. These steps occur before timing.

The measured region includes fresh per-query compilation, execution, answer
projection and complete ordered oracle comparison. No solved state is reused.
Models check the Minesweeper total and every overlapping 2x2 window; breadboard
models check physical holes, shorts, score and exhaustive optimum in the
bounded placement window. The optimum model takes circuit net pairs/rows and
selected wired nets from the Reference answer, so its independent optimum is
conditional on those fields. Full ordered parity separately checks all terms.
The [preceding report](engine-major-2026-10-18.md#loaded-program-method)
provides further detail about this unchanged runner.

```sh
cabal build exe:infera test:infera-test bench:core-major bench:core-engine --offline --enable-optimization=2
cabal list-bin bench:core-major --enable-optimization=2
# Run the returned executable from the matching checkout:
/path/to/core-major --case minefield-16 --batch 8 --timeout 60 +RTS -T -RTS
```

## Results

Median CPU milliseconds per fresh query; speedup is baseline/candidate.
Allocation change is candidate relative to baseline. Values below 1x retain
regressions. Wall times and GC counters remain in the raw rows.

| Case | Before ms | After ms | Speedup | GHC allocation |
| --- | ---: | ---: | ---: | ---: |
| `controls` | 0.139 | 0.141 | 0.99x | +0.0% |
| `guards` | 2.058 | 2.078 | 0.99x | +0.0% |
| `deep-index` | 4.837 | 4.849 | 1.00x | +0.0% |
| `liveness` | 13.204 | 13.250 | 1.00x | +0.0% |
| `table-cycle` | 0.056 | 0.050 | 1.12x | -0.8% |
| `table-cycle240` | 0.963 | 0.867 | 1.11x | -6.1% |
| `core-nrev` | 8.375 | 8.448 | 0.99x | +0.0% |
| `core-loop` | 10.246 | 10.216 | 1.00x | +0.0% |
| `core-fib` | 42.415 | 42.938 | 0.99x | +0.0% |
| `core-queens` | 9.035 | 9.018 | 1.00x | +0.0% |
| `breadboard-rc` | 1.543 | 1.659 | 0.93x | -2.2% |
| `breadboard-div` | 1.944 | 2.087 | 0.93x | -3.8% |
| `breadboard-tri` | 3.826 | 4.146 | 0.92x | -8.1% |
| `breadboard-wide` | 9.594 | 10.803 | 0.89x | -13.7% |
| `minefield-16` | 33.693 | 22.251 | 1.51x | -39.4% |

The Minesweeper case generates 50 bombs on a 16x16 grid, with at most two bombs
in every overlapping 2x2 window. Breadboard covers RC, divider, transistor and
three disconnected parts over a wider 1..16 column range. Ordinary pure
workloads are mostly within 0-1.5% of baseline; no broad pure-language gain is
established. The table cases improve locally with no CLP work in their bodies.

The [initial validation pairs](../data/jsonl/engine-mutable-clp-initial-2026-10-18.jsonl)
precede the final source. They exposed mixed breadboard costs. The complex
bridge subsequently stopped comparing the entire watched set after each
reduction and now imports watches using dirty variable IDs. The final table
still retains the breadboard regression. Initial rows are excluded from ratios.

The mutable representation introduces IORef lookups, trail writes and cache
invalidation, while complex constraints cross into persistent reducers.
Untimed counters below establish how much of each kind of reduction executes;
they do not isolate CPU cost by function. Further attribution needs profiling.
Native complex reducers and reducing redundant trail writes are the next
specific candidates, gated by these same models and parity tests.

RTS final sampling/GC bookkeeping contributes to allocation deltas, with that
forced GC outside CPU/wall timing. Process maximum live bytes in the loaded
matrix include loading, Reference and preflight, so they are not isolated Core
live-heap measurements or process RSS.

## Native path and memory evidence

[Untimed native counters](../data/jsonl/engine-mutable-clp-counters-2026-10-18.jsonl)
use initial Core collection limit one and reject fallback, errors and
exhaustion. Each query produces one answer. Counters are disabled in normal
execution and in all timings above. Raw rows include the probe source and
binary identity.

| Case | Propagation calls | Native linear reductions | Pure complex reductions |
| --- | ---: | ---: | ---: |
| Breadboard RC | 43 | 226 | 41 |
| Breadboard divider | 69 | 345 | 60 |
| Breadboard transistor | 216 | 1,237 | 166 |
| Breadboard wide | 353 | 5,136 | 1,149 |
| Minesweeper 16x16, 50 bombs | 656 | 1,568 | 0 |
| Seeded Minesweeper 10x10, seed 42 | 476 | 3,140 | 0 |

The kernel regression performs 1,000 decreasing single-variable bounds,
speculative rollback and committed updates without intermediate freezing.
It asserts zero remaining undo history and zero live constraint cells after
every commit, at most two variable cells, and exact final persistent-store
parity. This catches retained dropped-CID cells and deferred snapshot deltas.

A separate [whole-process memory probe](../data/jsonl/engine-mutable-clp-memory-2026-10-18.jsonl)
repeats `X #<= N` in a deterministic decreasing loop. The small query first
passes Reference/machine/Core parity with forced collection. All larger runs
return exactly one answer with `X in inf..1`, without errors or exhaustion.
The source and commands are recorded in the rows:

```nprolog
<- notable.
loop 0 _.
loop N X <- N > 0, X #<= N, M is N - 1, loop M X.
```

| Iterations | Baseline maximum live MiB | Candidate maximum live MiB |
| ---: | ---: | ---: |
| 10,000 | 8.19 | 8.19 |
| 100,000 | 8.19 | 8.19 |
| 1,000,000 | 8.19 | 8.19 |

These are RTS maxima from one fresh process per size/version, including setup,
not logical Core cell counts, process RSS or a universal space bound. The raw
one-million-update probe takes about 0.58 s baseline and 0.84 s candidate;
this is a retention check rather than a repeated timing matrix, but it also
shows the bookkeeping cost on small deterministic updates.

Commit reclaims history only when no Core choice survives. A live outer choice
keeps writes needed for rollback. Historical watched IDs, semantic
substitutions, retained answers and suspended search can still consume growing
memory; this experiment makes no bounded-space claim for those workloads.

## Correctness and release checks

The final runtime passes **429 properties / 27,369 cases across 43 groups**.
The new mutable group adds 150 generated operation/mark traces with exact
scheduler-store parity, 100 finite models, 50 generated complete small
minefields and seven fixed properties. Acceptance checks larger ordinary and
seeded minefields, overlapping multiple window rules, four independently
scored/optimized breadboards, tiny collection thresholds, retained answers,
atomic failures, aliases, nested control/minimums and imported stores.

The final example/parity sweep checks 416 queries under initial collection
limit one, with no fallback or skipped query. CLI diagnostics/trace/REPL
acceptance, 61 LSP tests and 34 benchmark-harness tests pass. Cabal package and
source-distribution checks include the new kernel, test module, parity fixture,
design document, report and raw data. No CLI default or constraint language
syntax changes in this stage.
