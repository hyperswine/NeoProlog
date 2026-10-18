# Current Core versus SWI-Prolog and Scryer

Date: 2026-10-18

At `c1a2ee3`, Infera's checked loaded-query CPU is **1.26-2.77x Scryer's**
and **3.92-10.09x SWI-Prolog's** on four ordinary untabled workloads.
Loop, Fibonacci and queens meet the requested roughly-2x target relative to
Scryer; reverse remains outside it. This does not establish a general language
or CLP performance ratio.

Fresh CLI results look closer because startup/loading are included: Infera is
faster than Scryer on loop, fib and queens, and takes 1.97x its time on reverse.
The earlier near-2x CLI assessment therefore cannot establish a uniform
startup-free performance bound.

## Loaded-query CPU

Median milliseconds per query from five measured fresh processes per
engine/case, after one additional validation process. Engine order rotates
across cases and rounds; all benchmarks and other checks run sequentially.
Each process performs a checked warmup outside timing and validates every
timed invocation. Lower is faster.

| Workload | Infera ms | SWI ms | Scryer ms | Infera / SWI | Infera / Scryer |
| --- | ---: | ---: | ---: | ---: | ---: |
| Reverse, 100 repetitions of 30 items | 9.023 | 0.894 | 3.262 | 10.09x | 2.77x |
| Counting loop, 90,000 iterations | 11.139 | 1.847 | 8.848 | 6.03x | 1.26x |
| Recursive Fibonacci, 25 | 45.104 | 10.680 | 29.156 | 4.22x | 1.55x |
| First valid 8-queens placement | 9.517 | 2.430 | 5.438 | 3.92x | 1.75x |

[Raw loaded samples](../data/jsonl/engine-external-loaded-2026-10-18.jsonl)
contain 72 successful rows: 12 validation and 60 measured samples. Batch sizes
are respectively 256, 256, 32 and 128 queries, identical across engines. All
batch CPU observations exceed 50 ms; no below-resolution timing or failed
result enters the table. Sample ranges and wall observations remain in the
rows. Scryer loaded wall time is unavailable and is not inferred from CPU.

Infera uses the unchanged `bench/core-major.hs`, which loads/checks source and
constructs a Reference oracle before timing. Its timed path creates a fresh
Core query, compiles predicate plans, executes, projects/forces observations,
checks an independent model and compares the complete ordered stream to
Reference. Core-only preflight rejects fallback. The NOINLINE nonce boundary
and varying unused query roots prevent sharing a solved Haskell result.

The external driver starts with an exact copy of `bench/bench.pl`, matching
Core's algorithms and inputs. It wraps each query in the same first-solution
policy, collects the result with `findall`, checks groundness and an independent
model inside each timed invocation, and prints/checks one final result outside
timing. The scalar/reverse results are exact; the queens model independently
checks bounds, distinct columns and diagonals. All cases are untabled.

These are loaded-query API costs. Infera currently compiles plans per query,
while SWI and Scryer compile source during loading. Model checking, result
collection and projection also differ between languages. This comparison does
not isolate instruction dispatch or assign the gap to one subsystem.

### Clock correction

An initial diagnostic matrix used SWI's compatibility `runtime` counter.
[SWI documents that this excludes garbage collection](https://www.swi-prolog.org/pldoc/man?section=builtin-statistics).
That matrix is excluded entirely. All three engines were rerun for the table
above, using SWI `statistics(process_cputime, T)` deltas, Core
`System.CPUTime.getCPUTime`, and Scryer `library(time):time/1` reported CPU.
The final comparison includes GC rather than subtracting it from SWI alone.

The clock audit checked official documentation and current upstream
[SWI process-clock code](https://raw.githubusercontent.com/SWI-Prolog/swipl-devel/master/src/os/pl-os.c),
[Scryer timing code](https://raw.githubusercontent.com/mthom/scryer-prolog/master/src/lib/time.pl),
[its system-call implementation](https://raw.githubusercontent.com/mthom/scryer-prolog/master/src/machine/system_calls.rs)
and the [cpu-time crate](https://docs.rs/cpu-time/1.0.0/src/cpu_time/clock_gettime.rs.html).
Exact installed release-tag sources could not be retrieved, so this report
does not assert identical OS syscall implementations in those binaries.
The older `bench/runtime-compare.py` targets the legacy Bytecode runner and
uses the compatibility timer; it was not used for these current Core results.

## End-to-end CLI wall time

Five checked measured fresh processes per engine/case after one checked warmup,
with rotating engine order. Times include startup, parsing/loading, Infera
inference/query compilation, solving, output and shutdown. Infera uses `-N1`.
Every process must exit successfully with exactly one independently valid
result and completion marker, without errors or exhaustion.

| Workload | Infera ms | SWI ms | Scryer ms |
| --- | ---: | ---: | ---: |
| Reverse, 3,000 repetitions of 30 items | 281.925 | 52.832 | 143.363 |
| Counting loop, 90,000 iterations | 32.896 | 18.397 | 57.908 |
| Recursive Fibonacci, 25 | 58.837 | 51.094 | 78.958 |
| First valid 8-queens placement | 31.956 | 19.209 | 55.113 |

[Raw CLI samples](../data/jsonl/engine-external-cli-2026-10-18.jsonl) contain
72 successful processes, including warmups, using `bench/run.py`'s unchanged
execution and validation functions. The reverse input is **3,000 repetitions
here and 100 in the loaded table**. Their absolute times are not directly
comparable. Startup/loading costs materially influence the short CLI cases.

## Identities and reproduction

Installed versions are **SWI-Prolog 10.0.2** and **Scryer cargo:0.10.0** on
macOS arm64. Infera is **2.0.0**, GHC 9.8.2, optimized library/runners (`-O2`),
revision `c1a2ee3eee8a88734c2ec8e6f28a5dae1225a349`. Its sorted
`src/**/*.hs` path/NUL/bytes/NUL SHA-256 is
`47864b82eefdb35382e8de1913cfdbdf733db5b2cd2d4106825a6399ee6ad405`.

Rows retain binary hashes, source/runner hashes, commands, batch sizes,
round/order, host and UTC time. All source and binary hashes were checked again
after each matrix. The
[provenance record](../data/jsonl/engine-external-provenance-2026-10-18.jsonl)
contains both orchestration scripts, the standalone Prolog driver and parser,
clock references, and hashes of the raw matrices. The driver/helper files were
temporary comparison artifacts; no runtime or maintained benchmark source was
changed for this measurement.

The Core runner can be reproduced from this revision with:

```sh
cabal build bench:core-major --offline --enable-optimization=2
cabal list-bin bench:core-major --enable-optimization=2
/path/to/core-major --case core-nrev --batch 256 --timeout 60 +RTS -T -RTS
```

The provenance record's `source_files` contains the external driver and Python
helpers. Recreate those files together in a temporary directory and adjust
recorded local executable/repository paths before replaying the recorded
commands. The CLI orchestration calls the maintained validation functions;
the loaded orchestration invokes the unchanged Core runner and external driver.

## Scope and next target

There is no maintained equivalent external breadboard, Minesweeper or tabling
fixture in this comparison. The measured 34% Minesweeper CPU reduction in the
[mutable CLP report](engine-mutable-clp-2026-10-18.md) compares Infera versions,
not Infera with these other solvers. CLP competitiveness remains unmeasured.

Reverse is the clearest remaining gap in this ordinary workload set. Existing
source evidence supports allocation-time variable lifetimes and frame/slot
reuse as candidates; these results do not yet measure their potential gain.

## Follow-up: what appears to explain the remaining gap

Current source points to repeated call/goal dispatch, head matching and
activation bookkeeping as the leading ordinary-execution candidates. Every
clause still allocates and initializes all logical variable slots before
matching ([Run.hs](../../../src/Infera/Core/Run.hs), `tryClause`;
[Store.hs](../../../src/Infera/Core/Store.hs), `allocSlots`). Tail calls can
reuse continuations, but still create another activation. Liveness currently
removes dead roots at collection time; it does not implement allocation-time
slot reuse.

The engine interprets boxed Haskell `Goal`, `Pattern` and `Expr` plans. Calls
build arguments, inspect normalization and signature/commit state, check depth
and collection thresholds, select clauses and match their heads. These are
source-confirmed operations, not a current function-level CPU attribution.
The current four-workload ratios are consistent with that overhead being
especially costly when each logical call does little work.

SWI documents dedicated compilation/selection cases for one-clause predicates
and empty-list/nonempty-list pairs, shapes used throughout reverse and append.
Its [indexing and body-unification documentation](https://www.swi-prolog.org/pldoc/man?section=jitindex)
provides concrete examples of avoiding general machinery for common patterns.
This supports specialized call/head/body paths as a candidate; it does not
quantify how much of reverse's 10x gap they explain.

Fresh source-matched setup probes and the existing five measured CPU samples
separate some tempting explanations:

| Case | Eager setup ms/query | GHC allocation MiB/query | RTS GC fraction of CPU |
| --- | ---: | ---: | ---: |
| Reverse | 0.099 | 35.13 | 2.81% |
| Loop | 0.085 | 32.21 | 2.07% |
| Fibonacci | 0.086 | 141.34 | 0.82% |
| Queens | 0.085 | 36.33 | 1.66% |

[Raw setup probes](../data/jsonl/engine-external-setup-2026-10-18.jsonl) contain
three samples of 512 fresh preparations per case, including the probe source
and binary identity. Loading and query execution are excluded. Each sample
creates a fresh native machine through the returned first IO action, retains
only the newest action in an IORef, and varies unused query roots. After the
timed samples the final action is drained to exactly one rendered native
answer, rejecting errors, exhaustion or abandonment. The complete independent
answer models remain in the external comparison above.

This measures the eager `runCoreWith` preparation boundary. Pure plan/proof
work may be forced during execution; it is not a complete compiler profile.
The measured eager cost is small against the 9-45 ms full queries here.
Compilation caching remains relevant to very short queries and larger loaded
programs, rather than being established as the main cause of these ratios.

Allocation includes fresh-query capacity: the initial uninitialized Core
cell array alone reserves about 8 MiB. The setup probe allocates about 8.17 MiB
per preparation. These totals are not amounts of boxed Prolog terms, live
memory or resident pages. Logical activation cells are written into that
array; they do not each correspond to a separate Haskell allocation.

Standard RTS GC alone cannot explain a 4-10x CPU gap at these fractions.
Allocation still has a cost, and Core's own mark/compact collector runs as
ordinary mutator code, outside those RTS GC fractions. Its current CPU share
has not been isolated. Historical pre-optimization profiles must not be used
as current percentages.

The next focused experiment is current-Core execution profiling, followed by
allocation-time slot/frame reuse and fused common call/head/arithmetic paths.
The four external benchmarks use no CLP and no tabling, so improvements to
those subsystems will not directly close this particular gap. Runtime safety
checks should be removed through proofs, preserving error and rollback
semantics; neither their total cost nor a Haskell-language ceiling has been
established by these measurements.
