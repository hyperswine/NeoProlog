# Next Core optimization priorities

Status: open follow-up from the 2026-10-31 audit of runtime `f6ac3be` against
pre-JIT `74c1740`. The examples and regression checks added later that day
extend coverage but do not fix the issues below. This is an implementation
plan, not a record of completed fixes.

The recent CPU improvements are repeatable across the original workloads and
the [five new example workloads](2026-10-15-PERFORMANCE.md#cross-theme-example-programs---2026-10-31).
The next optimization should make those gains sustainable in long-running
processes and protect them against regression before expanding the JIT fragment.

| Priority | Work | Completion criterion |
| --- | --- | --- |
| First | Boxed-value ownership and reclamation | Completed queries do not accumulate runtime boxes in a cached program |
| First | JIT code ownership and program-cache lifetime | Unreachable code mappings are released; alternating live programs reuse their images |
| Next | Interpreter allocation | Localize and remove the unexplained per-call increase, with measured budgets |
| Alongside each fix | Regression gates | CI detects lifetime regressions and inactive native kernels; repeatable benchmarks protect CPU and allocation |

## 1. Reclaim runtime boxed values

**Reproduced finding.** [Store.hs](../src/Infera/Core/Store.hs) routes `box`
through `boxIn (symbols s)`. The program-wide table appends runtime floats,
large integers and strings as well as compiled constants. Completed queries
therefore leave their boxed values reachable while the program remains cached.

The audit loaded one program:

```prolog
<- notable.
calc X Y <- Y is X + 0.5.
```

It ran `calc 1.0 Y?` through `calc 1000.0 Y?`, fully consumed each result,
checked `Y` against the independently calculated float, discarded the results,
then forced a full GHC GC. Repeating the same batch produced:

| Point | `boxCount (scopeSymbols scope)` |
| --- | ---: |
| After program compilation | 0 |
| After 1,000 completed queries and full GC | 2,000 |
| After 2,000 completed queries and full GC | 4,000 |

This demonstrates retained table entries, not just temporary allocation.
The measured probe used floats; large integers and strings share the same
append path and need dedicated regression coverage.

**Implementation direction.** Separate immutable program constants from
query-owned runtime boxes, or introduce equivalent ownership-aware reclamation.
Preserve the meaning of every `BOX` word baked into a shared compiled image.
Resetting the shared table at query completion would be unsafe for other live
queries and compiled constants. Choose and document the representation before
changing indices or collection.

**Acceptance criteria:**

* Promote the repeated-query probe to a durable test. After warmup, batches of
  discarded results must not produce linear growth in retained runtime boxes.
* Cover floats, integers outside the immediate range, strings, failed queries,
  backtracking and abandoned searches, with full GC between batches.
* Keep earlier answers and partially consumed search streams alive while later
  queries execute. Their values must remain correct; reclamation must wait for
  their owners to become unreachable.
* Preserve shared constants across queries and program reloads. Run reference
  parity and forced Core collection in all JIT/stream configurations.
* Report live boxes and retained memory separately from allocated bytes. A
  lower allocation total alone does not establish bounded retention.

## 2. Own JIT mappings and avoid recompilation on program alternation

**Source finding.** [Jit.hs](../src/Infera/Core/Jit.hs) installs native code
through `infera_jit_alloc`, retaining raw address/function-pointer fields in
`JitKernel`. It does not retain an executable-memory owner with a release
action. [infera_jit.c](../cbits/infera_jit.c) defines `infera_jit_free`, but
there is no Haskell import or call connecting it to the kernel lifetime.
The scratch-buffer `ForeignPtr` owns the scratch buffer, not the code mapping.
This finding is based on ownership-path inspection; the audit did not measure
a native-mapping RSS growth curve.

**Reproduced cache finding.** [Compile.hs](../src/Infera/Core/Compile.hs)
uses a single `IORef (Maybe ProgramScope)` entry. Repeated access to program A
reused its symbol table; accessing B and then A produced a different table for
A, even with the original program values still alive. Alternating programs
therefore rebuilds images and can repeatedly allocate native code that lacks a
cleanup path.

**Implementation direction.** Give executable mappings explicit ownership,
including the allocation size needed for release. Keep that owner alive across
every native call. Define program-image cache ownership and eviction together:
consider program-owned images or a cache with weak ownership or a documented
bound. Replacing one strong entry with an unbounded strong map would exchange
recompilation for another retention problem.

**Acceptance criteria:**

* Record mapping allocations, live bytes and releases in a test-only interface.
  Repeated load/run/drop/GC cycles must return to a bounded live-mapping level.
* Test two live programs alternately: after warmup, both reuse their compiled
  images within the supported cache capacity. Also test eviction and reload.
* Release mappings exactly once, including partially failed installation;
  never release code still reachable from an active query or native invocation.
* Verify lifecycle behavior on supported AArch64 and x86-64 hosts. Keep graceful
  interpreter fallback when executable allocation or CPU eligibility fails.
* Retain occurs-check, overflow, capacity, bailout and trail-restoration parity.

## 3. Remove the interpreter allocation regression

**Measured finding.** The [JIT activation report](2026-10-30-JIT-ACTIVATION.md)
records Fibonacci allocation rising from **67.81 MB to 82.30 MB per query
(+21.4%)**, despite lower CPU time. Fibonacci has no native kernel in this
fragment. The [week comparison](data/tsv/engine-week-2026-10-30.tsv) also shows
guards rising from **17.558 MB to 18.173 MB (+3.5%)**. The fresh audit reproduced
both allocation increases at `-O2`.

The activation report isolates a further useful diagnostic: with native
execution disabled, increasing a countdown query from 1,000 to 101,000
iterations gives **48 bytes per iteration before the change and 136 bytes now**,
an extra 88 bytes per call. Its experiments did not localize the allocation.
Do not treat the earlier stream-dispatch/codegen explanation as established:
the later report explicitly records failed attempts to reproduce that cause.

**Investigation and acceptance:**

1. Establish a reproducible profiling build with profiled dependencies, or use
   allocation/ticky evidence and compiler dumps to identify the extra object
   and allocation site. Measure fixed setup cost separately from per-call slope.
2. Use the same compiler, optimization profile, workload and RTS settings for
   before/after runs. Isolate JIT and stream effects with explicit environment
   flags; keep profiling instrumentation out of final timing binaries.
3. Restore the pre-change allocation slope and Fibonacci/guards budgets where
   possible. Any retained increase needs a documented explanation and a new
   explicit budget supported by a measured benefit.
4. Check the whole 20-case `core-major` suite, including the five new examples.
   Preserve the large native wins and interpreter-only workloads. Keep full
   answer validation and forced-collection tests as correctness gates.

## 4. Gate the gains and prove native execution

**Current gap.** [.github/workflows/ci.yml](../.github/workflows/ci.yml) runs
semantic parity and structural checks. The new example work adds independent
checks in all four JIT/stream modes and checked `core-major` example smoke runs.
These are useful correctness gates, but they do not enforce the original
15-case CPU/allocation results or prove that a native kernel executed.
Setting `INFERA_JIT=1`, compiling a kernel, or obtaining correct answers is
insufficient: silent fallback can preserve semantics while losing the speedup.

**Required follow-up:**

* Add test-only native invocation/result counters. A known eligible countdown
  and list workload must successfully execute a kernel on each supported CI
  architecture. Unsupported platforms must be explicitly reported as skipped.
* Test entry decline and mid-span bailout separately from successful execution,
  and compare resulting answers with the interpreter. Cover full parity with
  both JIT and stream disabled; the existing tree-mode leg only disables the
  stream and may still execute native kernels.
* Add deterministic retained-box, executable-mapping and image-reuse gates
  from the first two work items. Add measured allocation budgets for representative
  JIT and interpreter-only workloads, scoped to compiler/platform/profile.
* Run repeatable CPU comparisons on a controlled runner or release performance
  job. Cover all 20 current cases, use warmup and interleaved repeated samples,
  and choose batches with at least 50 ms of CPU. Calibrate failure thresholds
  against observed variance before making them blocking gates.
* Archive source and binary identities, compiler/RTS settings, JIT/stream modes,
  validated answers, allocation, retention and CPU samples. Report cold loading
  and compilation separately from warm query execution.

Completion requires both bounded lifetimes and preserved measured performance.
Passing the new examples alone does not close these follow-ups, and faster
native workloads do not offset a regression hidden in interpreter-only paths.
