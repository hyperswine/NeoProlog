# Allocation-free Core clause selection - 2026-10-19

Branch `core-unboxed-control`, base `1f075ac`. Follows the
[control stacks report](2026-10-19-CONTROL-STACKS.md), whose profile put
`candidateClauses` at about 9% of Core time on Fibonacci. A ticky build
showed 40-96 bytes of GHC heap per call in selection: `[Int]` results from
IntMap lookups, list intersections, `filterM` over the leading integer
guards, and a `Maybe` per `argumentAtPath`.

## What changed

**Precomputed results.** `candidateClauses` now returns a `Candidates`
value: `NoCandidate`, `OneCandidate ordinal`, or `Candidates` holding two or
more ascending ordinals in an unboxed array. Each predicate builds these at
compile time:

* `pAll` (every clause) and `pOne` (one shared `OneCandidate` per ordinal);
* every `ArgIndex` entry (`aiFast`, `aiBoxed`, `aiOpen`) and every deeper
  `DecisionIndex` entry, with singletons shared through `pOne`;
* `pIntGuards`, now an array with one `Maybe IntGuard` per clause, plus a
  `pHasGuards` flag.

A call that only looks up results returns one of these shared values.
Intersections and the guard filter count survivors first. When the result
equals one of the inputs, is empty, or is a single clause, they return a
shared value and build nothing. Only a strictly smaller result of two or
more clauses builds a new array. `argumentAtPath` returns an unbound word
instead of `Nothing`; no index or guard decides on an unbound word, so the
result is unchanged.

**No per-call closures or thunks.** The selection steps (`principalKeys`,
`decisionKeys`, `keepGuards`, `guardHolds`, `lookupImmediate`,
`lookupBoxed`) are top-level functions. As local functions closing over the
store and predicate, they had been allocated on every call (the first
version of this change *raised* allocation 15-75% because of that). Other
fixes:

* The position counter is forced in every equation, so GHC unboxes it.
* Accumulators and lookups are strict.
* Guard results are returned with `pure $!` (they had been lazy thunks).

The same audit found two existing thunks on the call path, now strict:

* a selector thunk for `mStore m` in `callClausesWithFrame` (24 B per
  call), created because selection was lazy in the store for unindexed
  predicates;
* the return-check rewrite of `cont` in `enterClause`.

**Choice cursor.** `AltClauses` holds the call's candidate array. The
position of the next candidate is a new unboxed mark field (`markNext`,
mark stride 5). `pushChoiceWithStore` sets it to 1. Backtracking reads it,
then either advances it or pops the choice before the last candidate, as
before. It no longer allocates a new `AltClauses` for each retry. The
tabling delta path converts its clause list into an array. That path is
not hot.

## Semantics kept

* Candidate order: results are always ascending.
* CLP-active calls (`rCLP /= 0`) still intersect every principal key, even
  after one candidate remains. They skip deeper decisions and guards.
* Boxed keys still go through the value map, and NaN still makes no index
  decision.
* Deeper decisions and int guards run only for pure calls with two or more
  principal candidates. The guard filter also applies when decisions leave
  a single candidate, as before.

One intentional shortcut: a pure call to an indexed predicate with at most
one clause returns `pAll` without reading arguments. Before, its principal
keys could reject the clause before the head ran. With no constraint store
active, the head performs the same checks, and a mismatch leaves no
binding or heap growth behind the failure, so the observable result is the
same. All parity checks below agree.

## Ticky check

With a `-ticky -ticky-allocd` build of `bench:core-major`, the runtime
entries for `candidateClauses`, `principalKeys`, `decisionKeys`,
`intersectCandidates` and `guardHolds` show 0 bytes allocated on reverse,
loop, Fibonacci and queens. `callClausesWithFrame` allocates only when it
pushes a choice (saved arguments and the `AltClauses` record). Its
per-call selector thunk is gone, so loop and Fibonacci show 0 bytes there.
`tryClauseWithFrame` keeps one boxed frame base (16 B) when it does not
reuse a tail frame; `matchHead` and `runGoals` take it boxed.

## Measurements

`bench/core-major`, `-O2`, macOS arm64. Each cell is the median of nine
fresh processes per binary, alternating base and new runs. Base is a
binary built from `1f075ac`.

Batch 1 (comparable with the previous report):

| Workload | Base CPU ms | New CPU ms | Change | Base alloc MiB | New alloc MiB | Change |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Reverse, 100 x 30 | 8.62 | 8.63 | +0% | 24.7 | 18.5 | -25% |
| Loop, 90,000 | 9.28 | 9.46 | +2% | 20.6 | 12.4 | -40% |
| Fibonacci 25 | 42.12 | 41.69 | -1% | 112.8 | 64.7 | -43% |
| First 8-queens | 8.79 | 8.97 | +2% | 25.6 | 19.4 | -24% |
| `guards` (int-guard selection) | 2.35 | 2.37 | +1% | 19.6 | 16.7 | -14% |
| `deep-index` (nested decisions) | 5.42 | 3.24 | -40% | 41.3 | 18.0 | -56% |

Batch 20 (per query):

| Workload | Base CPU ms | New CPU ms | Change |
| --- | ---: | ---: | ---: |
| Reverse | 8.35 | 8.46 | +1% |
| Loop | 9.46 | 9.71 | +3% |
| Fibonacci | 41.52 | 41.55 | +0% |
| Queens | 8.71 | 8.87 | +2% |
| `guards` | 2.25 | 2.21 | -2% |
| `deep-index` | 5.40 | 3.13 | -42% |

GHC allocation falls 24-43% on the four major workloads and 56% on the
deep-index case. CPU is flat on reverse and Fibonacci. It is 1-3% higher on
loop and queens, and loop is consistently about +3% over repeated
15-process runs. That does not come from the strict `cont'` (reverting it
did not change it), the mark stride (a stride of 8 measured the same), a
fast path for intersecting with every clause, or inlining
`candidateClauses`. It may be code layout. The deep-index case, where
selection walks nested decisions, is 40% faster.

As the previous report found for control frames, removing nursery
allocation alone rarely shows up as CPU on these workloads: a GHC nursery
allocation is a pointer bump, and minor collections of dead control
records are cheap. Fibonacci's 43% drop in allocation leaves its CPU
unchanged. The CPU gain is where selection did real work per call:
intersections, nested lookups and list building.

## Validation

* Full Haskell suite: 496 checks (`CoreDecisionTest` reads the result
  through `candidateList`).
* `core-engine parity` over every example and parity file except blocks
  and database_access: 512 queries agree with the reference and the legacy
  machine, both normally and with `--gc-limit 1`.
* `python3 test/cli.py`: all six acceptance groups pass.
