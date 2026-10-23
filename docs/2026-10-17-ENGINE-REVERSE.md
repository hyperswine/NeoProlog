# Reverse hot-path optimization - 2026-10-17

The reverse workload now takes about 20% less loaded-program CPU time and
38% less GHC allocation. The complete Haskell suite and the forced-collection
example/parity sweep pass. A performance gap to SWI and Scryer remains.

## Baseline and method

The baseline is `e3082b3`, with unchanged executables copied before editing.
Both versions use GHC 9.8.2 on the same macOS arm64 host, the default `-O1`
library profile and `-O2` executable/benchmark profile. No program, predicate
declaration, answer ordering or benchmark algorithm was changed.

The workload is `bench_nrev 3000`: naive reversal of a 30-element list 3,000
times, followed by one final reversal for the answer. `bench/run.py` checks
the answer independently and rejects process failures, errors, exhaustion
and missing completion markers.

Two measurements were taken sequentially, without concurrent builds or test
suites:

* Seven fresh-process samples of each core version, alternating order each
  round. `core-engine time --core` measures core query compilation, solving,
  projection and rendering after program loading. The RTS allocation and
  maximum-residency figures cover the whole process. A separate run with
  `--core-no-gc` isolates execution without cell-store collection; it is not
  the production configuration.
* Five checked CLI samples per engine/workload, after one checked warmup.
  Each round alternates the complete engine order. These wall times include
  startup, parsing/loading, solving and output. Infera uses RTS `-N1`;
  comparison engines are SWI-Prolog 10.0.2 and Scryer 0.10.0.

The [loaded samples](data/jsonl/engine-reverse-loaded-2026-10-17.jsonl) and
[CLI samples](data/jsonl/engine-reverse-cli-2026-10-17.jsonl) retain binary and source
hashes, environment, sample order and individual timings. These are local
measurements, not portable performance thresholds or inference-rate claims.

## Diagnosis and changes

The fresh baseline cost-centre profile attributed 15.4% of time and 21.0%
of allocation to the cell collector, 13.4% of time to `unifyPattern`, 11.1%
to `buildArg`, and 6.8% to `matchHead`. Profiling durations themselves are
not used as benchmark timings.

`Core.Store` now reserves a structure's complete cell block once. The common
two-field case, including cons, writes its fields directly. `Core.Run`
inlines slot/constant operations separately from recursive compound handling;
two first-occurrence head fields are matched directly. General constructor
filling accumulates groundness in a tail loop and stops inspecting it once
a non-ground child is known. A fresh first-occurrence head variable proves
its two-field constructor non-ground without checking either child.

Matching a structured head against an older unbound input still performs an
occurs check. It checks reused head slots instead of walking the newly built
graph: first-occurrence slots are fresh and cannot contain that older input.
The optimization is guarded by the input's allocation age; otherwise the
original graph check runs. Raw variable references remain in constructed
terms, preserving shallow control syntax and rollback behavior.

The collector's mark-stack height now lives in its unboxed array. Trail
compaction records entry widths backwards in the prefix-forwarding array,
then compacts forwards, eliminating the boxed list of entry triples and its
boxed counter. Variable resets and old-value entries, including ground-memo
restoration, retain their original representation and order. Forwarding and
trail-prefix arrays are reused per query and grown when needed. Bitmaps
remain freshly bulk-cleared: clearing a retained bitmap bit by bit was
slower in the intermediate experiment. Scratch arrays contain no logical
roots; every active forwarding entry is overwritten before it is read.

## Results

Median loaded-program samples:

| Reverse 3,000 x 30 | Before | After | Change |
| --- | ---: | ---: | ---: |
| CPU, collection enabled | 0.457 s | 0.365 s | 20.1% less |
| GHC allocation per process | 1,613,845,176 bytes | 1,001,577,416 bytes | 37.9% less |
| Maximum residency per process | 63,785,776 bytes | 52,679,136 bytes | 17.4% less |
| CPU, cell collection disabled | 0.357 s | 0.285 s | 20.2% less |

The production improvement therefore includes faster execution and cheaper
collection; it does not come from disabling or delaying collection. Scratch
storage is retained for the query's lifetime, bounded by the largest
collection workspace it has needed. It is released with the query.

Median checked CLI wall seconds:

| Workload | Infera before | Infera after | SWI | Scryer |
| --- | ---: | ---: | ---: | ---: |
| Reverse 30 x 3,000 | 0.507012 | 0.414145 | 0.067955 | 0.174463 |
| Counting 90,000 | 0.030458 | 0.032639 | 0.023815 | 0.072290 |
| Fibonacci 25 | 0.076985 | 0.077236 | 0.063343 | 0.097553 |
| Eight queens, first solution | 0.031191 | 0.031408 | 0.024324 | 0.065119 |

Reverse's CLI median falls 18.3%; the median same-round before/after ratio
is 1.22x. It remains 2.37x Scryer's and 6.09x SWI's CLI time. Those ratios
include startup and cannot be read as VM throughput ratios. The other cases
show no established improvement: their medians differ by 0.2-2.2 ms, and the
counting samples include a 43 ms after-sample. Larger loaded batches are
needed before drawing conclusions about such small differences.

## Validation

* `cabal test all --offline --test-show-details=direct`: PASS, all 38 groups,
  391 properties and 26,241 generated/example test executions. This run
  completed through the final opaque-scope group with exit status zero.
* `core-engine parity --gc-limit 1 examples/*.nprolog test/core/*.nprolog`:
  all 296 inline queries agree with Reference and Machine, with no fallback
  reported. The tiny initial threshold exercises relocation as live state
  grows; the collector still uses its adaptive threshold after collection.
* `python3 test/cli.py`: all CLI, live-buffer, trace, shipped-example, DCG,
  dynamic-declaration and module acceptance checks pass.
* `INFERA_BIN=... npm test --prefix lsp`: 61/61 pass, including the later
  dependency-aware checking and CLP hover regressions.
* `python3 -m unittest discover -s test -p '*bench_harness_test.py'`:
  34/34 pass.
* Both benchmark matrices complete without rejected samples; `git diff
  --check` passes.
* `cabal sdist` succeeds; the tarball includes all eight core parity fixtures
  and this report's sample files.

The new `parity-structures.nprolog` covers repeated head variables, nested
constructors, cyclic bindings, aliased inputs/outputs, failed alternatives,
raw arithmetic syntax, scalar variants, findall and constrained bindings.
Every fixture query is also replayed with forced collection in `CoreTest`.
A wide-structure regression grows the mark stack past its initial capacity,
then grows and reuses forwarding storage across temporary graphs.

The old 50,000-call declared-recursion differential case stalled validation
in the legacy evaluator. Its fixture now uses 1,000 calls, preserving the
three-engine contract comparison. A separate core-only regression still
checks all 50,000 calls against the independent sum 1,250,025,000, in normal
and frequent-collection modes, and checks that execution completes natively.
The large case was separated, not discarded.

## Remaining work

Reverse still pays for generic pattern interpretation, reference chains,
choice points and their live graphs, and remaining boxed results in the
driver. Further specialization should be justified by a new profile of this
version and checked against loaded, sufficiently long SWI/Scryer batches.
The current results do not justify claiming SWI/Scryer-level reverse
throughput.
