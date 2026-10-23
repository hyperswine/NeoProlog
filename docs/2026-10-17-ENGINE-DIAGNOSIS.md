# Engine diagnosis and foundation plan - 2026-10-17

This report records why the native machine is 50-200x slower than Scryer and
100-1000x slower than SWI-Prolog on the core workloads, what the profile
attributes that cost to, and the representation change that the next engine
step makes. The measurements are local, one process per sample unless stated,
and include startup, loading, solving and output. They are evidence for a
design decision, not portable CI thresholds.

## Measurements

Working tree at `4a78805` plus uncommitted edits, rebuilt with `cabal build`
(default library profile, which is `-O1`: the library stanza carries no
`ghc-options`; CI passes `--enable-optimization=2` explicitly and the Homebrew
formula does not). RTS `-N1 -s`. SWI-Prolog 10.0.2, Scryer 0.10.0. Inference
counts are SWI's `statistics(inferences)` for the same programs.

| Workload | Inferences | Infera | SWI | Scryer | Infera allocation | Per inference |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| nrev 300 x 30 | 168K | 2.10 s | 0.01 s | 0.05 s | 7.57 GB | 45 KB |
| loop 90000 | 180K | 0.53 s | 0.01 s | 0.05 s | 2.70 GB | 15 KB |
| fib 25 | 486K | 3.26 s | 0.03 s | 0.07 s | 12.4 GB | 25 KB |

GC is 10-20% of Infera's time in these runs; the mutator does the rest. A WAM
allocates tens of bytes per inference. Allocating 15-45 KB per inference is
the whole explanation of the gap: the machine performs many separate pieces of
work for each call rather than a slow version of one piece.

A stale `dist-newstyle` executable from 2026-10-16 11:48 (before the Step 1
public switch) ran the same three workloads 3-7x faster than the current
source. The current machine is a throughput regression against that build,
which agrees with the pre-migration CLI baseline recorded in
[performance.md](2026-10-15-PERFORMANCE.md).

## Profile

A `-fprof-late` cost-centre profile of the rebuilt library (`cabal build
--enable-profiling --profiling-detail=late`) on the nrev and fib workloads is
flat: the top entry is 9.4% and the next twenty entries are each 1-6%. No
single function dominates. The entries group by cause:

| Cause | Representative cost centres (nrev / fib, %time) |
| --- | --- |
| Call-time export and walks of every argument | `normArithTerm` 9.4, `special` in `requiresNormalization` 9.3, `callPredicate` 4.8, `exportRawTerms` 4.4 / 3.8, `deepWalk` 1.8, `termVarIds` 1.3 |
| Template import per activation | `importTerm` 6.3 / 8.6 (11-14% of allocation), `allocateActivation` 3.3 / 5.9 |
| Cell access through pages, generations and views | `peekPaged` 4.1, `readCell` 3.7, `viewCell` 3.0, `viewRaw` 2.4, `allocate` 2.8 / 4.2, `writablePage` 1.1 / 3.1 |
| Persistent substitution mirror and CLP store | `applyBindings` 1.9 / 2.3, `bindingChanges` 1.4 / 1.9, `unify` 2.5 |
| Snapshots per choice/scope | `freezeHeap` 2.9 (fib), `copyReachable` 1.3 / 1.8 |
| Driver record churn | `prune` 2.7 / 6.1% alloc, `tryClauses` 1.8 / 2.4, `runGoal` 1.2 / 3.1 |

## Where the work comes from

Every user predicate call in
[Control.hs](../src/Infera/Machine/Control.hs) `callPredicate` does the
following before any clause is tried:

1. Exports the goal from the heap to a `Term` (`Bridge.exportRawTerms`), then
   walks it with `normArithTerm`, which tests `f `elem` arithOps` (a `String`
   list) at every compound node, then walks the whole argument graph again in
   `requiresNormalization`, whose local `special` does another string-list
   membership test per node.
2. Deep-walks every argument through the persistent substitution to decide
   tail eligibility (`Tail.eligibleArguments` scans the result for `$cut`) and
   inferred commits. For `app RT [H] R` with a 29-element `RT`, the list is
   copied on every call, so each naive-reverse inference costs O(n). This is
   why reverse is 220x behind Scryer while the counting loop is 54x behind.
3. Mirrors every accepted binding into the immutable `IntMap Term`
   substitution of the CLP store (`Machine.CLP.unifyUsing` via
   `Bridge.bindingChanges`), even when the program posts no constraints. The
   heap is not the source of truth; it is one of two.
4. Runs builtins on `Term`s: `is` and comparisons in
   [Builtins.hs](../src/Infera/Machine/Builtins.hs) receive exported terms,
   walk the substitution, evaluate, and return a `Unify` that is imported back
   into the heap.
5. Freezes the heap at every choice point and opaque scope. A freeze copies
   each page written since the previous freeze (256 boxed cells), and the next
   write copies the page again. `fib` creates a clause choice on nearly every
   call.
6. Pays for the cell representation on every read: two `STRef`s, an `IntMap`
   page lookup, a boxed `Maybe`, a `Slot` box and an `Integer` generation
   check. Addresses are boxed pairs with `Integer` generations, compounds hold
   `[Address]` lists, functor interning uses `Map (String, Int)`, and every
   write appends a three-field trail entry whether or not a choice point can
   undo it.
7. Rebuilds the 24-field `Running` record and the `Branch` record on every
   driver step, and `prune` rebuilds the task list on every commit.
8. Still renames clause templates per activation on the public path: the
   interpreted driver is the default, and `importTerm` is the largest single
   allocator on both profiles.

Items 1-4 and 7 are avoidable within the current representation and are
worth doing in any design. Items 5, 6 and 8 are the representation itself.
The bytecode backend removes part of 8 but, as the Step 2 reports record, has
not produced a general win because the other seven costs remain.

## Decision

Step 1 optimised for immutability of every intermediate state, complete
provenance and residency proofs, and it pays for those on every inference.
No incremental change to that machine reaches Scryer; the per-inference
allocation shows that. The next step is therefore a new resolution core with
the representation every production Prolog uses, built beside the existing
machine, validated against the reference for parity on the subset it
supports, and extended until it carries the whole language. The existing
machine stays the public engine until then and remains the fallback for
anything the core does not yet support.

### The core (`Infera.Core`)

* **Cells** are unboxed tagged `Int` words in one growable unboxed array.
  Tags: `REF` (self-reference when unbound), `STR` (address of a functor
  cell), `FUN` (functor id and arity packed), `INT` (61-bit immediate),
  `ATM` (atom id), `CHR` (code point), `BOX` (index into a boxed table for
  bignums, floats and strings). A structure is a functor cell followed by its
  argument cells. Lists are ordinary `cons/2` structures, exactly as the
  parser produces them.
* **Atoms and functors** are interned once, when the program is compiled,
  into dense integer tables. Runtime interning happens only for constants
  created by builtins.
* **Binding** writes one word. **Trailing** records the address only when it
  is older than the newest choice point (`addr < HB`). Backtracking resets
  the heap top and unwinds the trail to the saved marks.
* **Choice points** are small strict records holding the heap top, trail
  top, continuation, cut barrier, output-log length and the remaining
  alternatives. There are no snapshots: branch-local state (bindings, output
  log) is restored by unwinding, not by copying.
* **Clauses are compiled once** per program into head-matching instructions
  and body plans over activation variable slots, with the existing
  any-argument indexing computed from dereferenced argument cells. Activation
  variables live in heap cells allocated at clause entry; body goals name
  them by offset from the activation base. A call constructs its arguments
  from those slots and matches the callee's head against the argument
  registers without building a head term. The last goal of a body continues
  with the caller's continuation, so deterministic tail loops run in constant
  control-stack space.
* **Arithmetic and comparisons** evaluate from cells: an `is` right-hand side
  is an expression plan over slots and never becomes a term. Integer results
  that fit stay immediate; bignums and floats box.
* **Control** (`,`, `;`, `->`, `!`, `not`, `once`, `call/N`, `findall`,
  `forall`) runs inline in the same machine with cut barriers, the standard
  way. Errors become `BranchError` items followed by failure, preserving the
  reference's ordering of answers and errors.
* **Contracts** keep their reference semantics: declared mode/sort checks at
  call and return, `det`/`semidet`/`multi` commits and failure checks, and
  inferred semidet commits when the inferred switch arguments are ground at
  call time. The groundness test walks heap cells. A trailed ground-memo bit
  on structure cells is the planned refinement for predicates whose switch
  argument is a long list.
* **Arithmetic normalisation of call arguments** (the reference evaluates
  `fact (N - 1) R` as `fact 4 R`, including inside bound data) is preserved
  without a per-call walk: the compiler evaluates static arithmetic argument
  plans at construction time, and the machine counts arithmetic structures
  that programs construct as data. While that count is zero no call argument
  can contain one, so the normalisation walk is skipped; otherwise the
  reference walk runs.
* **The pure lazy `Search` boundary** is kept at the API: `solveQuery`
  returns a lazy list of immutable `SearchItem`s. Internally the core runs in
  `IO` and the list is produced by interleaved resumption of one mutable
  machine. Each `Found` exports the query variables' bindings as immutable
  terms at that moment, so retaining an answer while forcing the rest is
  safe, consuming a prefix is safe, and the element sequence is a function of
  the program and query alone. This replaces per-step heap freezing with an
  export per answer.
* **Fallback.** The core compiles a program only when every reachable
  construct is in its supported subset (initially: user predicates,
  contracts, control, unification, arithmetic, comparison, type checks,
  `write`/`writeln`/`nl`, `findall`). Tabled, dynamic, CLP, string, file and
  DCG-IO goals are outside it for now. A program outside the subset uses the
  existing machine unchanged. A construct detected only at runtime (for
  example `neq` on non-ground operands, which is a constraint) abandons the
  core run and the facade restarts the query on the existing machine, which
  is sound because solving is a pure function of the program and query.

### Acceptance for this step

* Exact ordered parity of `SearchItem` sequences (answers, errors, cut
  markers) with `Infera.Engine.Reference` on the benchmark programs, the
  control fixtures of `bench/machine-bytecode.hs`, and generated programs in
  the supported subset.
* Throughput on nrev, loop, fib and queens recorded with the same harness as
  the earlier reports, against the current machine, SWI and Scryer.
* Bounded control stack for deterministic tail loops. Heap growth in
  deterministic loops is accepted for this step and is the subject of a
  later compacting collector, as in every WAM.

### What this step does not do

It does not change the parser, inference, purity gate, CLP store, tabling
algorithms, REPL or diagnostics. It does not remove the existing machine or
the reference engine. It does not yet make the core the public default.

## First core slice - results on 2026-10-17

The core lives in `src/Infera/Core/` (`Store`, `Compile`, `Run`) with the
facade `Infera.Core`. It is opt-in: `Infera.Core.solveQuery` returns the
stream or Nothing, `solveQueryOrFallback` uses the existing machine
otherwise, and `coreSupports` names the construct that keeps a program out.
Public `Infera.Engine` entry points are unchanged.

### Parity

`test/core/parity-basic.nprolog` (31 queries) and
`test/core/parity-edge.nprolog` (49 queries) cover user predicates, indexing,
cut, disjunction, if-then-else, negation, `once`, `forall`, `findall` with
output and errors, `call/N` with cuts, declared `det`/`semidet`/`multi`
contracts with mode and sort errors, inferred semidet commits, arithmetic
including bignums, floats, division and exponent errors, lexical comparison
of atoms, characters and strings, type checks, output, unknown predicates and
occurs-check failures. The `core-engine` test group checks that every query
produces the same rendered answers, output, distinct errors and exhaustion
flag as both `Infera.Engine.Reference` and the current machine, and that the
facade falls back for a program outside the subset and for a runtime
disequality constraint. All pass. Internal variable names in error messages
match because each activation block carries a marker cell holding the
reference's fresh-id base.

### Throughput

`bench/core-engine.hs` (`cabal run core-engine -- time FILE "query?"`)
times one loaded program on the core, the machine and the reference, in
process, three runs each. Medians on the same macOS arm64 host, GHC 9.8.2,
default `-O1` library profile:

| Workload | Core | Machine | Reference | Core vs machine |
| --- | ---: | ---: | ---: | ---: |
| nrev 300 x 30 | 0.078 s | 1.916 s | 0.563 s | 25x |
| loop 90000 | 0.019 s | 0.492 s | 0.236 s | 26x |
| fib 25 | 0.072 s | 2.725 s | 0.461 s | 38x |
| 8 queens, first solution | 0.019 s | 0.594 s | 0.104 s | 31x |

Full-size runs on the core alone with `+RTS -s`:

| Workload | Inferences | Core | Rate | GHC allocation | Max residency |
| --- | ---: | ---: | ---: | ---: | ---: |
| nrev 3000 x 30 | 1.68M | 0.79 s | 2.1M/s | 2.9 GB | 135 MB |
| loop 1000000 | 2.0M | 0.21 s | 9.6M/s | 1.9 GB | 34 MB |

The roadmap's provisional target of 2 million verified inferences per second
on naive reverse is met by this first slice. Against the external
engines measured above (SWI 0.02 s and Scryer 0.09 s for the same reverse
workload, process time), the core is roughly 8x behind Scryer and 40x behind
SWI. GC time is negligible; the remaining cost is mutator work and GHC
allocation of about 1.7 KB per inference: argument lists, continuation
records, `Either`/`Maybe` arithmetic results and `IntSet` candidate
selection. Residency grows with deterministic work because the store has
no collector yet, as expected for this step.

### Progress after the first slice (same day)

* Ground memo bits, a precomputed index, an integer fast path, argument
  registers and a non-allocating goal loop took naive reverse 3000 from
  0.79 s to 0.33 s (about 5M inferences per second); loop 90000 to 0.009 s,
  fib 25 to 0.040 s, queens to 0.011 s.
* A mark-compact collector of the cell store runs at call boundaries when
  the heap exceeds an adaptive threshold. The parity group replays every
  query collecting at nearly every call. Reverse 3000 now holds 57 MB
  instead of 135 MB (the retained part is the program's own `range` choice
  points) at 0.46 s; a million-iteration loop holds 8.6 MB.
* Programs are no longer rejected whole: a tabled or dynamic predicate, a
  constraint goal, `minimize` or a dynamic-fact goal abandons the core run
  when reached, and the facade continues on the existing machine, skipping
  the prefix already produced. Leaf builtins (strings, characters,
  formatting, DCG text helpers, file reads) run through the reference
  implementation on exported terms with bindings imported back; `phrase`,
  `phrase_from_file`, `emit` and `call/N` run natively in alias blocks.
  Across `examples/`, 47 of 85 inline queries complete on the core and
  every query agrees with the reference after fallback.

### Language coverage (same day, later)

The core now runs the whole language that the examples and parity programs
exercise; every inline query in `examples/` and `test/core/` completes on
the core with no fallback and agrees with the reference, also when the
collector runs at every call (`core-engine parity --gc-limit 1`).

* **Tabling** is native: the reference's branch-local variant table and
  linear fixpoint, with dependency, error and exhaustion items in the
  reference's order, answers replayed with their output, and tables saved
  in choice points. Calls and answers that touch constrained variables use
  plain evaluation, as the reference does.
* **Dynamic facts**: `assert`, `retract`, `retractall` and calls to
  flag-declared names use a branch-local fact map.
* **`minimize`** is a sentinel scope that records the cheapest solution's
  trailed bindings to older cells, output, tables, facts and store, and
  reinstates them when the search is exhausted.
* **Constraints** keep the persistent `Infera.CLP` store, branch-local in
  choice points. Store goals, labeling and branch-and-bound are delegated
  to the reference's own goal functions on exported terms with the store
  passed in and out, so propagation is the same code. The core owns
  bindings: once a store exists, `bind` records bound cells, and at the
  next goal boundary the watched ones are fed to `applyBindings`; bindings
  the propagator made are installed back on the heap. Variables are
  exported with their marker-based logical ids, so a variable keeps one
  identity across goals; the collector retains the activation block of
  every live slot that is unbound or still undoable, so those ids survive
  compaction. Programs without constraints pay one register test per
  binding and per goal boundary.
* **Leaf builtins** (strings, characters, formatting, DCG text helpers,
  file reads) are delegated the same way; `phrase`, `phrase_from_file`,
  `emit` and `call/N` run natively in alias activation blocks.

Costs after this: naive reverse 3000 is 0.54 s with collection and
0.38 s without (the hooks above cost about 15% on the hot path, the
collector's block retention the rest); loop 90000 0.013 s, fib 25 0.054 s,
queens 0.014 s. Not yet on the core: interactive tracing (`--trace`), which
still runs on the existing machine.

### The core is the public engine (same day, evening)

`Infera.Engine.solveQuery` now runs on the core with fallback to the
machine, which switches the CLI, the REPL and every test that solves through
the public API. The complete suite passes (including the generated
correctness models, tabling, CLP, breadboard and minesweeper groups), the
CLI acceptance passes, and the validated CLI harness
(`python3 bench/run.py`, one warmup and three timed processes, medians,
process time including startup and loading) records:

| Workload | Infera (core) | SWI-Prolog 10.0.2 | Scryer 0.10.0 | Infera before (machine) |
| --- | ---: | ---: | ---: | ---: |
| reverse 30 x 3000 | 0.700 s | 0.052 s | 0.140 s | 20.155 s |
| counting loop 90000 | 0.030 s | 0.017 s | 0.056 s | 0.446 s |
| fib 25 | 0.068 s | 0.050 s | 0.076 s | 2.318 s |
| 8 queens, first | 0.030 s | 0.018 s | 0.053 s | 0.572 s |

The "before" column is the machine's loaded-program CPU time from the
opaque-control report, so it excludes startup and flatters the old engine.
Infera's process startup is about 20 ms of each figure. The core is now
ahead of Scryer on three of the four workloads and within 2x of SWI there;
naive reverse remains 5x behind Scryer and 13x behind SWI, with the
remaining cost in the collector's work for the program's retained choice
points and the boxed intermediate results on the hot path. The goal-level
entry points (`solveGoal`, `solveGoals`) and `--trace` still use the
machine.

Collecting at four times the live size (above the floor) instead of twice
brought reverse to 0.47 s of process time for a few MB more residency.
Building the library at `-O2` (as CI does) gains a further 5% on reverse and
nothing on the other workloads, so the default profile is unchanged.
Inlining slot and constant arguments, precomputing the inferred switch
positions, and writing first-occurrence head variables instead of unifying
them then took the in-process figures to reverse 3000 0.42 s with
collection (0.32 s without), loop 90000 0.011 s, fib 25 0.047 s and queens
0.011 s. The profile of reverse without collection is now argument and
structure construction (22%), head matching (14%), goal dispatch (9%) and
unification (8%); the remaining allocation is boxed results of small
`IO Int` helpers, which is ordinary GHC tuning rather than design.

### Reverse follow-up and current next steps

The [reverse follow-up](2026-10-17-ENGINE-REVERSE.md) optimizes structure
construction, head matching and collection against `e3082b3`: loaded CPU
falls from 0.457 s to 0.365 s and GHC allocation falls 38%. The complete
391-property suite and all 296 forced-collection inline queries pass.
The report records the remaining SWI/Scryer gap and individual measurements.

Argument registers, immediate arithmetic, indexed selection, a compacting
collector, language coverage and the public-engine switch are implemented
as described above. Remaining work is further profile-guided specialization
of construction/matching and the driver, plus migrating tracing and the
goal-level APIs before retiring the old machine. Compare loaded batches
before making throughput claims from startup-inclusive CLI times.
