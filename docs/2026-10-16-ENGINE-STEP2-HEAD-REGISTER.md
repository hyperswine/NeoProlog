# Compiled head matching and register sharing - 2026-10-16

The foundation and Step 1 follow-up were committed and pushed as
[`d2b19f7`](https://github.com/hyperswine/NeoProlog/commit/d2b19f7a55048490c274207e580ad16a7b33cefc).
This follow-up implements specialized matching for supported first-order heads,
shared variable/scalar registers and deferred body construction. Bytecode remains
opt-in; the public `Infera.Engine` still selects the interpreted native driver.

## Implementation

[`Compile`](../src/Infera/Compile.hs) emits a flat preorder head program:
`HeadVariable`, `HeadConstant` and `HeadCompound`. Compound instructions retain
their arity, construction slot and subtree width. A separate immutable postorder
construction plan has constant-time indexed access, shared across activations.
Generated compiler checks independently decode both programs and verify widths,
register dependencies, exact source identities and scalar bits.

[`Bytecode.activate`](../src/Infera/Machine/Bytecode.hs) matches that program
against the caller heap. Known compound shapes are inspected directly, without
constructing a duplicate head. A free caller target constructs only the required
source subtree and uses ordinary occurs-checked unification. Typed scalar
matching preserves atom/zero-arity-compound distinctions and numeric `Double`
equality: signed zeros unify, while NaNs fail even when a handle is shared.

All head writes reach `NativeCLP.unifyUsing` in the same depth-first order as a
single structural unification. Propagation runs once, after the whole head
matches. An earlier temporary binding cannot raise a delayed constraint error
when a later head field mismatches. A matching head with that error still
reports it. Only a head accepted by both unification and CLP constructs body
graphs; output checks and successful-body commitment remain in the driver.

The whole-head transaction owns leaf writes. The trusted
`Heap.unifyWithChangesInTransaction` helper runs the unchanged unifier without
duplicating a checkpoint for each leaf. It retains full trailing, occurs checks,
write order and NaN behaviour. Its caller must restore the enclosing checkpoint
on failure; ordinary public heap unification retains its own atomic wrapper.
An outer activation transaction additionally owns local roots, constructors and
interning, and removes them on mismatch, heap error or CLP error.

Construction registers reuse repeated local variables and immutable scalar
values. Float keys use exact bits, so signed zeros and distinct NaN payloads stay
separate. Compounds keep distinct source slots. A matched caller compound never
becomes a body construction register: its caller IDs could change observable raw
body syntax. The temporary array is allocated lazily, and fully known facts can
match without allocating it. Stable logical roots still reserve the exact
original local-ID range, including the owner ID for ground clauses.

Normal `activate` performs no instruction-statistic writes and returns zero
statistics. `activateMeasured` collects counts for accepted activations only;
failed head work is excluded. `Control` selects the measured variant only when
metrics are enabled. New counts report head instructions, known head constructor
cells avoided and maximum temporary-array slots. No mutable register or counter
escapes an activation or frozen checkpoint.

## Validation

The final `-O2` build and all **326 Haskell properties / 22,690 cases** passed.
All 37 LSP tests, CLI diagnostics/live-buffer/tracing/example checks and the
20 benchmark-harness tests also passed.

The new head group adds 500 generated comparisons against the legacy
rename/import plus whole-head unification path on independent thaws of the same
frozen heap. Comparisons include exact raw substitution IDs and scalar bits,
all persistent CLP metadata, raw and dereferenced bodies and accepted local-ID
sets. Focused cases cover:

* Known heads with no head-constructor or temporary-array allocation, and free targets
  that construct only the required source fragment.
* Repeated variables, typed scalars, NaN payloads, signed zero and register reuse.
* Complete rollback on mismatch, occurs failure, stale handles and overflow.
* A large body remaining unallocated when its head fails.
* Whole-head CLP propagation, including delayed division/type errors masked by
  a later mismatch, and reported after complete structural success.
* Retained/interleaved snapshots and normal/measured execution parity, including
  zero normal counters and independent later bindings.

An additional 10,000-iteration structured-head driver case compares Reference,
Interpreted and Bytecode results, checks the independent sum, exercises head
instructions and collection, and bounds live tasks and heap cells. Existing
three-engine tests retain contracts, explicit fuel, dynamic facts, tables,
opaque-control fallback, exact source traces and retained search resumes.

`cabal check` and `cabal sdist` passed. All 94 source, test, benchmark and
documentation files were checked byte-for-byte against the source archive.
Package checking retains the existing optimization-option and dependency-bound
warnings.

## First-order measurements

Local macOS arm64, GHC 9.8.2, Cabal library and runners `-O2`. Each row uses one
checked warmup and three checked timed runs. Programs are parsed and checked
before timing; cold per-query code/cache construction, execution, full draining,
projection and validation are included. Distinct unused logical-variable bases
prevent sharing evaluated searches between samples. Exact ordered Reference
observations and independent arithmetic/list models must both pass.

| Workload | Reference median | Interpreted median | Bytecode median |
| --- | ---: | ---: | ---: |
| Helper dispatch, 10,000 iterations | 0.080723 s | 0.213599 s | 0.239292 s |
| Structured list, 300 entries | 0.118829 s | 0.395796 s | 0.369723 s |
| Structured heads, 10,000 iterations | 0.098121 s | 0.306139 s | 0.316388 s |

The structured-list case is faster in these samples, while helper dispatch and
the structured-head case remain slower. No general throughput win is
established, and the public default remains unchanged. These small local runs
are reports rather than portable CI thresholds.
[Raw samples](data/tsv/engine-step2-head-register-2026-10-16.tsv).

Untimed measured probes prove compiled execution occurred. The structured-head
case executes 210,004 head instructions and avoids 80,001 duplicate head
constructors across 20,001 accepted activations. The complete fixture's
construction plan uses 84 pooled slots instead of 135 source-node slots, a
38% reduction. Its largest actual temporary array has 23 slots; stable local
roots are counted separately. This is register sharing and lazy allocation,
rather than full argument/environment lifetime trimming.

The [initial matcher samples](data/tsv/engine-step2-head-register-initial-2026-10-16.tsv)
are retained with their own fingerprint. They motivated removing per-leaf
checkpoints and normal-mode statistic writes. The
[foundation samples](data/tsv/engine-step2-bytecode-2026-10-16.tsv) remain historical and
use a smaller loaded fixture; do not derive cross-version speed ratios from
those different programs and source snapshots.

## Compiled residency

All 28 fresh-process Bytecode samples passed the existing residency bound:
peak process RSS and RTS maximum live bytes remain within 1.5 times the 10k/100k
prefix maxima. The matrix includes repeated million-iteration mutual recursion,
live alternatives and `findall`, plus helpers, structured arguments, live CLP,
completed tables and dynamic facts. Ordinary and measured modes are checked
separately; every unmeasured counter remains zero.

Peak RSS ranges from 125.95 to 128.11 MiB. Measured active heaps stay at or below
1,033 cells, with at most five tasks and two choices. The tail matrix's largest
temporary array has 11 slots, excluding stable logical roots. Retaining earlier
answers or growing output deliberately retains caller-owned memory.
[Raw compiled residency samples](data/jsonl/engine-step2-head-tail-2026-10-16.jsonl).

The default interpreted backend also passed the six-sample mutual/helper quick
matrix against the same runtime source. Its peak RSS ranges from 125.92 to
127.92 MiB, with at most 1,030 measured active heap cells.
[Raw default-backend recheck](data/jsonl/engine-step2-head-native-tail-2026-10-16.jsonl).

## Real CLP acceptance

The 16x16 minefield with 50 bombs and at most two bombs in every overlapping
2x2 window passes under both native backends. All searches are fully drained;
the exact Reference answers/residuals and independent dimensions, binary-cell,
bomb-count and all 225 window-cap checks pass. Setup remains unlabelled, so its
acceptance checks shape/cell aliases and exact Reference residuals instead.

| Loaded-program phase | Reference median | Interpreted native median | Bytecode median |
| --- | ---: | ---: | ---: |
| Constraint setup | 0.069964 s | 0.534934 s | 0.504770 s |
| Ordinary first grid | 0.084921 s | 0.594479 s | 0.566861 s |

Each row uses one checked warmup and three checked fresh processes, excluding
parsing/loading. An additional untimed measured Bytecode run verifies 8,443
accepted compiled activations, 43,825 head instructions and 14,772 avoided head
constructors. This prevents an entirely interpreted fallback from satisfying
compiled CLP acceptance. Differences between the native backends are small
relative to sample variability; both remain slower than Reference.
[Raw minefield samples and probe](data/jsonl/engine-step2-head-minefield-2026-10-16.jsonl).

## CI follow-up

The [published foundation run](https://github.com/hyperswine/NeoProlog/actions/runs/38865172911)
passed Ubuntu, including all foundation tests, large native minefield, bytecode
benchmark and residency gate. macOS selected the intended Xcode SDK but still
failed while building dependencies: the reused GHC package database contained
absolute Command Line Tools 27 SDK paths in its RTS/GHCi records. `SDKROOT`
could not override those explicit library directories.

The workflow now retargets only that selected GHC installation's SDK paths in
settings/package metadata, backs up originals under `RUNNER_TEMP`, refreshes the
package cache and checks that stale paths are gone. Static/threaded and dynamic
shared-library link probes run before Cabal builds. The runner's CLT and Xcode
installations remain intact. The approach uses GHC's documented
[package metadata and recache interface](https://downloads.haskell.org/ghc/9.8.2/docs/users_guide/packages.html);
the [setup action](https://github.com/haskell-actions/setup) can reuse installed
tools. YAML, shell/Python syntax, all eight actual local stale metadata
references, versioned/unversioned SDK paths and idempotence were checked without
modifying the local GHC installation. The revised hosted macOS workflow has not
run yet.

CI additionally checks the bytecode backend's quick million-iteration residency
matrix and the measured large minefield. Measured minefield checks require positive compiled/head counters;
unmeasured tail runs require every counter to remain zero.

## Remaining Step 2 work

Body graphs are still constructed for the complete accepted body rather than
one call at a time. Argument/environment register lifetimes, trimming, control
continuations, indexing instructions and persistent load-time code caches remain
planned. General table producers still rename/import their head/body templates
and use persistent head unification; their native callbacks select the requested
backend for subsequent activations. Existing caches remain per query or producer
startup. Wider differential acceptance and consistent throughput gains are
required before switching the default.

## Reproduce

```sh
cabal build all --offline --enable-tests --enable-benchmarks --enable-optimization=2
cabal test all --offline --enable-benchmarks --enable-optimization=2 --test-show-details=direct
"$(cabal list-bin bench:machine-bytecode --enable-optimization=2)"
"$(cabal list-bin bench:machine-minefield --enable-optimization=2)" --engine bytecode --phase ordinary --size 16 --bombs 50 --measured
python3 bench/check-tail-memory.py "$(cabal list-bin bench:machine-tail --enable-optimization=2)" --backend bytecode --output /tmp/infera-bytecode-memory.jsonl
```

Final runtime-source SHA-256:
`e19903429399e20bc31d014240cc9baade3b07e9c46abedcbe4cb77c595957e1`.
Individual runners also record their workload/dependency fingerprints and timing
scope. Historical files preserve their original build and source metadata.
