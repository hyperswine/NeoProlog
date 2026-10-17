# Operand materialization and invocation dispatch - 2026-10-16

This stage follows published predicate caching,
[`9a946ca`](https://github.com/hyperswine/NeoProlog/commit/9a946caf6be91c6d4cb306c951fa5f789264c49e).
It reduces local-operand setup, constructor transaction overhead and ordinary
invocation dispatch. Bytecode remains opt-in. Final-source targeted checks
pass, including the full local suite. Representative timings remain mixed,
with warm-control and breadboard regressions against interpreted execution.
All 36 local residency processes passed. This operand stage was published as
[`a58da56`](https://github.com/hyperswine/NeoProlog/commit/a58da56f6770ff5c9cbb9ce0fab99edc673efb87).
Cross-platform CI is a separate gate; intermediate runs are preserved separately.

## Implementation and ownership contracts

Opaque `DataPlan` values store ascending used source-local IDs once, with
runtime operands indexing a compact layout. Materialization resolves those
source IDs plus the activation base through strict `Bridge.lookupVariables`.
Plans with at most four locals read that already-checked list directly, with
at most three list-tail steps per read; larger plans use a private immutable
array. This removes the per-leaf `IntMap` and avoids an additional array for
common small plans. Bounds checks and strict environment/root validation
remain, including an empty lookup for ground plans.

Dense indices never become logical variable IDs. Compatibility accessors
decode through the immutable source-ID layout; GC liveness remains in source
IDs. Repeated operands retain their raw aliases, sparse IDs, signed zero, NaN
payloads and rewritten cut owners. Pending frames reacquire relocated roots
without retaining address arrays. Local-only, single scalar/owner and single
all-local constructor plans also avoid temporary register arrays. General
plans read every child before overwriting a recycled destination. Measured
body-register counts describe temporary arrays actually allocated.

`materializeDataWithMetrics` owns one outer heap checkpoint. Trusted
`Heap.importScalarInTransaction` and `Heap.newCompoundInTransaction` retain
scalar/raw-child validation, interning and allocation while avoiding another
checkpoint per node. Every failure rolls back the complete materialization,
including intern additions made before a failed allocation. Public
`importTerm`/`newCompound` remain atomic. Raw reference children remain dynamic
when bound; allocation generations do not rewind. Binding trails, occurs
checks, reference paths and whole-head CLP propagation order are unchanged.

For unmeasured, untraced invocation below the collection threshold, the driver
calls `runGoal`/`callPredicate` directly with the reached root and exposed
continuation. This avoids constructing and immediately popping a `Run` or
`DirectRun` task. With tail reuse disabled there is no active collection
boundary. At the threshold, or in measured/traced execution, the queued task
remains an explicit relocation root and preserves sampling/event boundaries.
`callPredicate` still roots its goal during a collecting tail transfer.
Existing handlers retain builtin precedence, dynamic/uncallable goals,
contracts, fuel, cuts and errors.

Measured production counters therefore describe the queued path. They verify
compiled plans, controls, caches and allocation behavior; they do not measure
the unmeasured fusion branch. Timings disable instruction counters, and
normal/measured parity checks exercise both paths.

Opaque-control protection now uses a strict outer `ProtectedRoots` constructor
with a lazy `IntSet` payload. `Bridge.bindingVariableSet` supplies exactly the
IDs represented by `bindingVariables`. Child launch unions the existing
protected set with the exact parent binding-ID set; only actual collection
converts it to an ascending list for `Bridge.rebuild`. A separate `NOINLINE
scopeProtectedRoots` helper extracts parent IDs and `Bindings` before forming
the lazy union. Short scopes avoid unused key-set work, and the thunk retains
those inputs without a selector closure over the complete parent driver.
The protected memberships, raw-substitution closure and snapshot/scope
ownership stay the same. The final-source residency checks below include
opaque compiled controls parked across a million-call helper.

## Validation status

The frozen final runtime is
`497c22dbae85ba4c09d61ad6aca50c71315a6144d81d79d3e843cc8aa058d6d1`.
It built successfully and passed **eight new operand properties / 606 cases**.
These cover independent dense/source/heap decoding, sparse operands in
controls/CLP, repeated locals, exact scalar bits/owners, stale empty lookups,
dead-root rejection, frozen alias writes, normal/measured collection, trusted
builder rollback and public atomicity.

The complete final-source Haskell suite passed **361 properties / 25,018
cases** across 35 groups. All **37 LSP tests**, CLI diagnostics/live-buffer/
trace/REPL/runtime-error/shipped-example checks and **20 Python harness tests**
also passed. The [broader bytecode benchmark](../data/tsv/engine-step2-operands-bytecode-2026-10-16.tsv)
passed all **27 engine/case rows and nine positive compiled probes** across its
nine fixtures. Cross-platform CI has not run for this candidate. CI now
includes warm control batches of 20 and breadboard batches of 10; configuration
is not evidence of a remote pass. Earlier-stage results are not substituted
for final-source gates.

Fresh-process residency passed all **30 bytecode** samples in the
[full matrix](../data/jsonl/engine-step2-operands-tail-2026-10-16.jsonl) and **six interpreted**
samples in the [quick comparison](../data/jsonl/engine-step2-operands-native-tail-2026-10-16.jsonl).
The compiled matrix covers mutual recursion, retained choices, findall, helper
calls, structured arguments, CLP, tables, dynamic state and parked compiled
controls, including normal and measured million-call runs. Every search fully
drained and satisfied the existing RSS and RTS maximum-live bound of 1.5 times
the prefix maxima. Compiled peak RSS ranged from 165,969,920 to 184,844,288 bytes;
maximum measured live heap size was 1,027 cells. Both matrices record the final
runtime SHA-256 and preserve their commands.

`cabal check` and `cabal sdist` passed. The check retains the existing `-O2`
and missing dependency-upper-bound warnings. Every source-archive file matched
the working-tree bytes, including the new tests, runners and all 27 operand
report/evidence files.

## Matched baseline and timing scope

The baseline core is exactly `9a946ca`: its 27 `src` files were independently
checked against that commit's Git blob IDs, with no changes. Both stages use
byte-identical updated `machine-cache.hs` and `machine-breadboard.hs` runners.
Preserved baseline binaries/source snapshots allow rebuilding the candidate
without losing the comparison. Local runs use macOS arm64, GHC 9.8.2 and
`-O2` for library and runners.

Parsing/checking, metadata forcing and the independently validated Reference
oracle occur outside timing. Cold is the first native/compiled query in its
process, with no compiled preprobe. Warm first drains one checked query
outside timing, then starts fresh solver states sharing immutable program
plans. Every timed query executes, fully drains, projects and validates its
complete ordered stream against Reference and an independent sum/grid model.
The cache runner's measured bytecode probe runs after timing. Reference has
already executed its oracle before every timer, so its cold label does not
mean its first execution in the process.

The final matrix uses **240 process records: 60 discarded process warmups and
180 measured samples**. Five cases (helpers with zero/1,000 padding predicates,
structured heads, controls and minefield) run cold/warm under all three engines
and both stages. Each group has three measured fresh-process samples, with
baseline/candidate order alternating within corresponding sample pairs. Warm
controls use batches of 100; other matrix rows use batch one. Breadboard uses
two rounds per stage, reversing stage order, with three checked batches of 100
per engine/case in each round. Those are stage blocks, rather than adjacent
per-batch pairs.

Batch one preserves historical forcing and unused-variable bases. Larger cold
batches are rejected. Warm batches pass unique nonces through `NOINLINE
executeBounded`, which cycles unused roots through bases 2-5 internally; solver
execution has a separate `NOINLINE execute` boundary. The caller cannot merge
distinct nonce applications by seeing the bounded base. No evaluated-search
cache exists in the runner. This is a source-level anti-sharing audit, not a
generated-Core claim. Each invocation starts fresh heap/store/table/dynamic
state and consumes/discards its result before the next query. Only the final
result is retained for the cache runner's answer fingerprint.

Cache `wall_seconds`/`cpu_seconds` are batch totals; explicit per-query fields
divide by batch size. Breadboard's existing columns are per-query batch
averages, with appended totals/samples. A batch average is not an individual
query latency distribution. Warmth includes ordinary CPU/runtime/GC effects
as well as immutable code reuse. Discarded process warmups do not share program
caches with the next process. A source-witness cache hit also does not prove a
plan had already been evaluated before that hit.

## Final acceptance measurements

The [final matrix](../data/jsonl/engine-step2-operands-2026-10-16.jsonl) completed all
**240 records / 180 measured samples**, and all four breadth processes passed.
Every matrix record passed status/full-drain/Reference/independent-model
checks. Workload and answer fingerprints match per case; all recorded runtime
hashes and the orchestration's final source/hash checks match the frozen
baseline and candidate. The 48 breadth rows and 16 untimed positive compiled
probes also passed, with zero predicate-cache misses.

Median wall seconds per query are below. Ratios compare corresponding
candidate/cache-baseline measured process pairs; a ratio below one favors the
candidate. Warm controls are batch-100 averages; other matrix rows use batch
one. The median of paired ratios need not equal the ratio of medians.

| Case / phase | Baseline bytecode wall | Interpreted wall | Bytecode wall | Paired wall ratio | Paired CPU ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| Helper 0 / cold | 0.165018 | 0.151015 | 0.162580 | 0.985 | 0.984 |
| Helper 0 / warm | 0.211060 | 0.206625 | 0.201007 | 0.952 | 0.950 |
| Helper 1,000 / cold | 0.186881 | 0.177957 | 0.172596 | 0.984 | 0.981 |
| Helper 1,000 / warm | 0.494961 | 0.165002 | 0.226730 | 0.720 | 0.669 |
| Structured heads / cold | 0.558405 | 0.353919 | 0.335834 | 0.601 | 0.735 |
| Structured heads / warm | 0.319975 | 0.340683 | 0.290907 | 1.237 | 1.197 |
| Controls / cold | 0.012541 | 0.012303 | 0.010639 | 0.777 | 0.795 |
| Controls / warm | 0.016429 | 0.010715 | 0.023412 | 1.425 | 1.161 |
| Minefield 16 / cold | 0.633354 | 0.733112 | 0.684065 | 0.876 | 0.881 |
| Minefield 16 / warm | 0.484805 | 0.516098 | 0.471232 | 0.992 | 0.993 |

There is no reliable general speedup. Cold control CPU improves alongside
interpreted execution: their paired ratios are 0.795 and 0.758. Warm control
CPU instead has bytecode ratio **1.161**, versus Reference **0.997** and
interpreted **1.022**. Its individual CPU ratios span 0.799-1.181, and wall
ratios 0.774-1.453. Bytecode's warm medians are 0.023412 wall / 0.017805 CPU
seconds, versus interpreted 0.010715 / 0.010251: **118.49% / 73.69% slower**.
That remains an acceptance issue despite the variation.

Warm zero-padding helper CPU is effectively tied with interpreted (0.194635
versus 0.194249 s). Warm padded helpers still trail interpreted 37.41% wall /
29.72% CPU, despite favorable candidate/cache pairs. Warm structured-head
aggregate medians favor the candidate, but paired wall/CPU ratios favor the
baseline and span both directions. Minefield warm paired CPU is essentially
unchanged at 0.993, while interpreted and Reference also improve slightly.
Raw individual samples preserve the outliers and phase-dependent drift.

The final small-local refinement improves the helper ratios compared with
the before-small-locals pass, but the control ratios worsen:

| Warm workload | Before-small wall / CPU ratios | Final wall / CPU ratios | Final paired CPU range |
| --- | ---: | ---: | ---: |
| Helper 0 | 1.516 / 1.297 | 0.952 / 0.950 | 0.845-1.084 |
| Helper 1,000 | 1.049 / 1.044 | 0.720 / 0.669 | 0.481-0.992 |
| Controls, batch 100 | 1.046 / 1.025 | 1.425 / 1.161 | 0.799-1.181 |

These are separate passes against the same source baseline, rather than a
controlled direct before/after comparison. Reference and interpreted ratios
also shift, and control ranges overlap. The results are compatible with a
helper/control tradeoff, but do not establish that the bounded-list change
caused it. They cannot support making bytecode the default.

### Breadboard

All placement geometry, net compatibility, independently enumerated optimum
and exact Reference-order checks passed. Raw rounds are baseline
[first](../data/tsv/engine-step2-operands-cache-baseline-breadboard-r1-2026-10-16.tsv) and
[second](../data/tsv/engine-step2-operands-cache-baseline-breadboard-r2-2026-10-16.tsv),
candidate [first](../data/tsv/engine-step2-operands-operands-breadboard-r1-2026-10-16.tsv)
and [second](../data/tsv/engine-step2-operands-operands-breadboard-r2-2026-10-16.tsv).
Pooled medians of six batch-100 averages, in seconds per query:

| Case | Baseline bytecode wall | Interpreted wall | Bytecode wall | Baseline bytecode CPU | Interpreted CPU | Bytecode CPU |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| RC | 0.006880 | 0.003891 | 0.004221 | 0.005316 | 0.003783 | 0.004084 |
| Divider | 0.006139 | 0.005755 | 0.005788 | 0.006037 | 0.005723 | 0.005765 |
| Transistor | 0.022079 | 0.014192 | 0.012652 | 0.017779 | 0.013663 | 0.012368 |
| Wide disconnected | 0.020008 | 0.015063 | 0.016873 | 0.018447 | 0.014496 | 0.016189 |

Against contemporary interpreted execution, RC is 8.50% wall / 7.94% CPU
slower, divider is essentially tied, transistor is 10.85% / 9.48% faster,
and wide is 12.01% / 11.68% slower. This is not an across-the-board breadboard
win. Cache-baseline improvements also require drift context: RC candidate/
baseline CPU round ratios are 1.222 then 0.531, while interpreted ratios are
1.264 then 0.620 and Reference ratios 1.154 then 0.761. Transistor favors the
candidate in both rounds, but the second round also improves Reference and
interpreted. The blocks cannot isolate every gain to the implementation.
The broader fixture gate and all 36 final-source residency samples pass.
Cross-platform CI remains a separate requirement.
Its pass does not remove the matched matrix or breadboard regressions.

## Archived refinement evidence

The intermediate artifacts preserve exploratory decisions and noisy results;
they are not pooled with the final candidate. Each full matrix contains
240 process records / 180 measured samples, and each breadth pass has two
reversed-order rounds with three batch-100 samples per engine/case.

| Intermediate runtime | Matrix | Breadboard rounds: baseline / candidate |
| --- | --- | --- |
| Before protected sets (`6f927f`) | [matrix](../data/jsonl/engine-step2-operands-before-root-sets-2026-10-16.jsonl) | [r1 baseline](../data/tsv/engine-step2-operands-before-root-sets-cache-baseline-breadboard-r1-2026-10-16.tsv), [r1 candidate](../data/tsv/engine-step2-operands-before-root-sets-operands-breadboard-r1-2026-10-16.tsv), [r2 baseline](../data/tsv/engine-step2-operands-before-root-sets-cache-baseline-breadboard-r2-2026-10-16.tsv), [r2 candidate](../data/tsv/engine-step2-operands-before-root-sets-operands-breadboard-r2-2026-10-16.tsv) |
| Eager protected sets (`ff29c3`) | [matrix](../data/jsonl/engine-step2-operands-eager-root-sets-2026-10-16.jsonl) | [r1 baseline](../data/tsv/engine-step2-operands-eager-root-sets-cache-baseline-breadboard-r1-2026-10-16.tsv), [r1 candidate](../data/tsv/engine-step2-operands-eager-root-sets-operands-breadboard-r1-2026-10-16.tsv), [r2 baseline](../data/tsv/engine-step2-operands-eager-root-sets-cache-baseline-breadboard-r2-2026-10-16.tsv), [r2 candidate](../data/tsv/engine-step2-operands-eager-root-sets-operands-breadboard-r2-2026-10-16.tsv) |
| Before small-local reads (`b41164`) | [matrix](../data/jsonl/engine-step2-operands-before-small-locals-2026-10-16.jsonl) | [r1 baseline](../data/tsv/engine-step2-operands-before-small-locals-cache-baseline-breadboard-r1-2026-10-16.tsv), [r1 candidate](../data/tsv/engine-step2-operands-before-small-locals-operands-breadboard-r1-2026-10-16.tsv), [r2 baseline](../data/tsv/engine-step2-operands-before-small-locals-cache-baseline-breadboard-r2-2026-10-16.tsv), [r2 candidate](../data/tsv/engine-step2-operands-before-small-locals-operands-breadboard-r2-2026-10-16.tsv) |

Initial dense/fused [control samples](../data/jsonl/engine-step2-operands-initial-2026-10-16.jsonl),
before trusted node allocation, showed only a 1.29% median reduction for
batch-100 controls: 0.01187361 to 0.01172045 s/query. Ranges overlapped:
0.01144132-0.01248821 versus 0.01137522-0.01263431 s. Initial batch-20
breadboard [baseline](../data/tsv/engine-step2-operands-initial-cache-baseline-breadboard-2026-10-16.tsv)
and [candidate](../data/tsv/engine-step2-operands-initial-dense-fused-breadboard-2026-10-16.tsv)
were mixed, including wide 8.34% slower than interpreted. These motivated
removing nested node checkpoints, rather than establishing a control win.

The before-set pass still had controls 18.83% cold / 23.69% warm slower than
interpreted. Its breadth timing had severe wall/CPU and round variation. The
eager-set pass had cleaner breadth samples but still lagged interpreted by
6.60% RC / 6.20% transistor / 20.63% wide wall time. Eager set construction
also computed protection for short scopes that never collected, prompting
the final lazy wrapper and metadata-only extraction.

The before-small-locals pass illustrates the need for paired evidence. Warm
control wall medians decreased 18.38% against cache bytecode, yet median
paired wall/CPU ratios were **1.046 / 1.025**, with paired CPU range
0.925-1.261. Warm zero-padding helpers regressed in every pair: CPU ratios
1.227-1.442, wall ratios 1.372-1.705. Its RC breadth CPU also lagged interpreted
13.16%. Those were remaining acceptance issues, not results to discard as
noise. Direct bounded reads now avoid an extra local array for plans using
at most four locals; the final run evaluates that source candidate separately.

All archived full matrices and breadth placement/optimum models passed their
answer checks. Corresponding workload and answer fingerprints matched.
For example, controls use workload `ae40cc5ac70d2d51ddc699cc7a622a45` /
answer `7b0d817a3d558a04c1f428e22b65da86`; minefield uses
`0b652a8c1cec54625d88745292c33046` /
`8204cc1bdf3867bc465496ecaeb004c4`. Host/runtime/GC variation remains visible;
reversing stage order does not make this a controlled runner or attribute
every difference to the implementation.

## Default migration and fingerprints

Bytecode remains opt-in. Migration still requires complete generated/API/
stdlib and trace parity, rollback and retained/interleaved snapshot checks,
final-source residency, cross-platform CI, and matched cold/warm representative
performance. Helpers, heads, controls, minefield and all four breadboard cases
remain inputs. The [roadmap gates](../../engine/roadmap.md#making-bytecode-the-public-default)
retain explicit interpreted selection and Reference. Intermediate gains do
not resolve outstanding representative regressions.

Runtime source SHA-256 values:

```text
cache baseline  5ab0407026c7cd5fb445007188be0765ed37eb21f3fe4d3576e1b5f1e72ecdd1
dense/fused     5281627b01290fb9a1248bd192c90ea99f1de32ec485ec8f68f6129cbb91d821
before sets     6f927f2398c712760cf2855988cc0a7e19b3d198e75e68b48de7952bd0ef2480
eager sets      ff29c3351122584b0f0a159f26e24a20fd9ceb64909f9415e067e1bd6ba16105
before small    b411643d00dfc99727ce7838a33255712388aedf1d3923d79e9a80097ca23a1d
final           497c22dbae85ba4c09d61ad6aca50c71315a6144d81d79d3e843cc8aa058d6d1
```

## Reproduce

```sh
cabal build bench:machine-cache bench:machine-breadboard --offline --enable-benchmarks --enable-optimization=2
"$(cabal list-bin bench:machine-cache --enable-optimization=2)" --engine bytecode --phase cold --case controls
"$(cabal list-bin bench:machine-cache --enable-optimization=2)" --engine bytecode --phase warm --case controls --batch 100
"$(cabal list-bin bench:machine-breadboard --enable-optimization=2)" --batch 100
```
