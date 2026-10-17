# Step 1 acceptance and Step 2 handoff

The native abstract machine now supplies the public solver. Step 1's local
correctness, immutable-search and eligible-tail residency gates pass. Step 2
has a prepared interface with both the native machine and retained reference
interpreter as semantic oracles. A later application check found a large-minefield
regression that should be resolved before bytecode implementation starts.
General throughput has not improved;
dispatch, term construction and boundary conversions remain substantial costs.

These results describe the local working tree on macOS arm64, GHC 9.8.2, with
the library, executable and benchmark runners built using Cabal
`--enable-optimization=2`. CLI measurements use RTS `-N1`. Remote CI has not
verified this snapshot. These checks ran locally before publication.
The older reference baseline used a different
library optimization profile, so its CLI times are historical context, rather
than a controlled estimate of the native/reference ratio.

## What closed the remaining Step 1 work

* `Infera.Engine` routes public solving through `Machine.Control`.
  `Engine.Reference` preserves the previous resolver and supplies shared
  public result types; the machine does not call its resolver.
* Ordinary builtins, dynamic facts, file/DCG operations, general `minimize`
  and native variant/delta tables complete the earlier control and CLP work.
  Table producers execute native callbacks and expose immutable canonical
  answer iterators. They are not producers sharing the caller's active heap.
* Frozen heaps now own each saved choice, sub-search and continuation. Restoring
  them reinstalls the matching immutable pages before execution. Tests retain,
  repeat and interleave old answers and checkpoints across later collections.
* Tail eligibility proves the closed pure first-order call graph, including
  mutual recursion and prefix helpers. Declared delayed checks, success
  obligations, effects, meta/control goals, dynamic/tabled callees and cuts keep
  conservative frames. Pure noncommitting calls can retire while internal
  retries remain parked; committing transfers still require their entry depth.
* Active-branch collection preserves caller/query IDs, pending contracts,
  opaque-scope terms, raw alias links and complete CLP metadata. Raw graph
  relocation preserves shared suffixes rather than copying them repeatedly.
  Safe points also reclaim completed non-tail activations. Unreachable
  historical activation substitutions are pruned; caller IDs and reachable
  alias syntax remain observable.
* Loader source maps, immutable trace batches, logical frames and located
  runtime errors now reach the REPL and CLI in trace mode, including imports,
  DCGs and table callbacks. Tracing is opt-in; interactive per-port stepping
  is future work.
* Compiler-owned performance hints and unsafe/dynamic editor annotations remain
  covered by the shared CLI/LSP tests.

The residency gate found real retention defects that machine counters alone
missed: disabled trace thunks captured retired callers, lazy guard updates
retained old choice lists, and redundant cut clamps retained old barrier
expressions. Strict optional trace fields, eager owned-guard updates and no-op
commits remove those histories. Reverse additionally exposed an internal
`range` retry blocking noncommitting tail retirement and causing collection to
repeatedly scan growing return stacks. The final transfer rule fixes that case
without discarding its pending retries or late errors.

## Correctness and integration checks

| Check | Local result |
| --- | --- |
| Full Cabal build, tests and both benchmark targets, `-O2` | Passed |
| Haskell/Hedgehog suite | 278 properties, 20,698 cases passed |
| LSP suite using the rebuilt compiler | 37 tests passed |
| Benchmark-harness unit tests | 20 tests passed |
| CLI, live-buffer and shipped-example diagnostics | Passed |
| CLI/REPL tracing and located runtime errors | Passed |
| Breadboard circuits, exact answers and independent physical optima | Passed |
| Fresh-process residency matrix | 28 checked samples passed |
| Validated CLI benchmark matrix | Four cases passed, one warmup and three runs each, 60s budget |
| Source archive contents and packaged extension runtime | Passed; exact current file bytes verified |

Generated comparisons cover ordered answers, errors, output, residuals,
exhaustion, table metadata, dynamic versions, constraints and rollback. Independent
models cover unification, finite CLP, graph closure, breadboard placement and
late-error order. The six parked-retry properties add 353 cases and preserve
committing success barriers while checking bounded active frames and independent
resume behavior. All nine original general-tail properties remain in the suite.

Commands used for final validation:

```sh
cabal build all --offline --enable-tests --enable-benchmarks --enable-optimization=2
cabal test all --offline --enable-benchmarks --enable-optimization=2 --test-show-details=direct
INFERA_BIN="$(cabal list-bin exe:infera --enable-optimization=2)" npm test --prefix lsp
python3 test/cli.py "$(cabal list-bin exe:infera --enable-optimization=2)"
python3 -m unittest discover -s test -p bench_harness_test.py
python3 bench/check-tail-memory.py "$(cabal list-bin bench:machine-tail --enable-optimization=2)" --output docs/performance/data/jsonl/engine-step1-tail-2026-10-16.jsonl
"$(cabal list-bin bench:machine-breadboard --enable-optimization=2)" > docs/performance/data/tsv/engine-step1-breadboard-2026-10-16.tsv
python3 bench/run.py --binary "$(cabal list-bin exe:infera --enable-optimization=2)" --engine infera --runs 3 --warmup 1 --timeout 60 --json
cabal sdist
```

The CLI JSON file additionally records the runtime source SHA-256 and build
profile. The residency script records that hash itself and rejects runtime
source changes during the matrix. Measurements run serially after builds and
tests, with one fresh process per residency sample. The source hash is
`a8ccf6ab9afb053748fe7d7801b100e20241298d4a043af6497ddc8ed7c26104` across all 24 runtime Haskell files. Before publication, one surplus blank line at EOF was removed from
`Machine/Table.hs`; no executable code changed. The packaged runtime source hash
after that whitespace cleanup is `fb35c3fb99a10eb56db85991aa90300f98c8bae433f7b7c5d86018d941af0959`. Benchmark rows retain
the exact source hash measured, and the native table tests were rerun after cleanup.

## Residency and throughput evidence

All 28 samples passed. Peak RSS was **126.8–127.9 MiB**; measured active heaps
stayed at or below **1,037 cells**. Million-call ordinary execution:

| Case | Median seconds | Samples |
| --- | ---: | ---: |
| Mutual recursion | 10.236 | 3 |
| Surviving caller choice | 10.226 | 3 |
| Inside findall | 10.383 | 3 |
| Prefix helper | 18.061 | 1 |
| Structured shared input | 13.672 | 1 |
| Live CLP state | 10.823 | 1 |
| Completed table | 10.539 | 1 |
| Dynamic state | 10.390 | 1 |

Breadboard wall-time medians on the same build:

| Case | Reference ms | Native ms | Native / reference |
| --- | ---: | ---: | ---: |
| rc | 0.906 | 3.858 | 4.26x |
| div | 1.534 | 6.970 | 4.54x |
| tri | 3.735 | 16.447 | 4.40x |
| wide-disconnected | 9.267 | 12.399 | 1.34x |

CLI wall-time medians (one validated warmup, three validated timed runs):

| Case | Median seconds |
| --- | ---: |
| nrev | 32.551 |
| loop | 0.752 |
| fib | 4.168 |
| queens | 1.311 |

Reverse now validates in 32.551 seconds median, after exceeding 120 seconds
before the parked-retry fix. The 30-second budget would still reject it. The
60-second final budget records current behavior explicitly; it does not
establish an acceptable production latency or a throughput win.

The [residency data](../data/jsonl/engine-step1-tail-2026-10-16.jsonl) include 10k, 100k and
three ordinary million-call runs each for mutual recursion, a surviving caller
choice and `findall`, followed by instrumented million-call runs. Helpers,
structured arguments, CLP state, completed tables and dynamic state each have
ordinary and instrumented million-call samples. Every process verifies and
fully drains its result. Normal execution has all counters disabled. CI uses
the same script's six-sample mutual/helper subset and checks RSS and RTS
maximum live bytes against 1.5 times the prefix-process maxima.

Process maxima include startup and runtime fingerprint construction. They are
not directly comparable with early samples that fingerprinted fewer source
files. Active-heap counters exclude independently frozen heaps. A workload
that deliberately retains growing outputs, answers, traces or pending retries
can retain proportional memory; the bounded total-residency claim concerns the
fixed-live-state cases in this matrix. Parked internal-retry tests separately
prove bounded active frames while preserving legitimately growing alternatives.

The [breadboard data](../data/tsv/engine-step1-breadboard-2026-10-16.tsv) measure already
loaded checked programs, projection and validation, with one checked warmup and
three checked runs per engine/case. Exact answer order matches the reference;
each result also matches an independently enumerated physical optimum. These
small cases remain slower on the native engine. There is no general speedup
claim or portable elapsed-time threshold.

The [CLI data](../data/jsonl/engine-step1-cli-2026-10-16.jsonl) include startup, loading,
solving and output. Every warmup and timed process must validate the expected
result and completion marker. The final budget is explicitly 60 seconds per
process. Earlier [30-second results](../data/jsonl/engine-step1-cli-before-tail-retries-2026-10-16.jsonl)
and the [120-second reverse timeout](../data/jsonl/engine-step1-nrev-before-tail-retries-2026-10-16.jsonl)
are preserved with their previous runtime fingerprint. They preceded the
parked-retry fix and contain no invented timing samples for failed runs.

## Step 2 starting contract

An additional [application recheck](../README.md#current-native-engine-recheck---2026-10-16)
after the architectural closeout found 16x16 ordinary minefield generation
exceeding 30 seconds, versus 2.163s before the earlier optimizations and 0.116s
on the optimized reference stage. Current graph closure and wide breadboard
medians are 0.099s and 0.053s. These observations use different historical build
profiles and are not controlled cross-version ratios. The minefield timeout is
a material regression missed by the Step 1 correctness/residency matrix.
Profile and resolve it before starting the compiler/VM work, and retain it in
future performance checks. [Raw samples](../data/jsonl/performance-step1-2026-10-16.jsonl)
include the failed sample and current source hash.

Start with compiled facts and first-order rules over the existing machine:

1. Add a clause compiler and bytecode dispatcher while retaining native
   interpreted execution as a selectable oracle. Preserve source identities
   and trace/error frames through instruction offsets.
2. Compare complete ordered observations against both Step 1 and Reference,
   including failure after partial binding, contracts, cuts, late errors,
   repeated/interleaved resumptions and CLP/breadboard acceptance.
3. Measure clause/head/body construction, dispatch, normalization, projection
   and checkpoint costs separately before choosing packed cells or registers.
   The current boxed paged heap and persistent CLP mirror are correct starting
   points. Allocation-prefix environment witnesses and constant-time validation
   are already implemented. Packed WAM cells, general trailing elision and
   compiled register/environment frames remain future work.
4. Keep the fresh-process residency gate, complete suite and validated benchmark
   harness in CI. Retain Reference through Step 2 and a full parity release.

Eligible tail loops have no fixed resolution-depth bound. Explicit-fuel APIs
retain their original budget, and calls excluded from tail reuse keep their
existing conservative limit. Interactive debugger stepping, same-active-heap
table producers and broad representation changes are separate work. None is
claimed by this local Step 1 exit gate.
