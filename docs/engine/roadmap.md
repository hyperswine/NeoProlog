# Engine roadmap: from a lazy-list resolver to an abstract machine

This records the earlier machine/bytecode implementation and its migration
gates. The public query engine has since moved to `Infera.Core`; start with
the [current engine guide](README.md) and
[performance overview](../performance/README.md) for its present behavior.

This is the plan for replacing the resolution core of Infera in two steps:

1. **An explicit abstract machine** (`Infera.Machine`): mutable bindings with a
   trail, an explicit goal stack and choice-point stack, last-call
   optimisation, bounded live memory for deterministic tail calls, and hooks
   for tracing. Same source language and observable query behaviour.
2. **Bytecode compilation** (`Infera.Compile`, `Infera.Machine.Bytecode`):
   progressively replace clause-template traversal with instructions executed
   by the machine from step 1, caching lazy plans with immutable predicate versions.

Everything above the engine keeps its public behaviour: the parser,
declarations and inference
([Infer.hs](../../src/Infera/Infer.hs)), the purity gate, the CLP(Z) store's
propagation logic, DCG translation, the REPL, `infera check`, the LSP and the
test suite. The engine's public surface is kept so that nothing downstream
changes: `solveQuery` returns `Search`, a lazy list of `SearchItem` values
including `Found SolverState`; `projectAnswer`, `solveAll` and `runInfera`
provide the higher-level answers. The exported `SolverState`, `SearchItem`,
`Env`, `solveGoal` and `solveGoals` interfaces used by tests and adapters also
remain compatible. Internal loading metadata and the CLP binding interface
will need extensions described below.

## Why

The original harness did not check process success or answers; its timings
are withdrawn as an acceptance baseline. The validated harness recorded the
following local medians on 2026-10-16, with one checked warmup and three
checked timed runs per workload and engine:

| workload | Infera | SWI-Prolog | Scryer |
| --- | --- | --- | --- |
| reverse a 30-element list 3,000 times | 6.188 s | 0.051 s | 0.139 s |
| counting loop to 90,000 | 0.268 s | 0.017 s | 0.056 s |
| `fib 25`, untabled | 0.463 s | 0.046 s | 0.076 s |
| first valid 8-queens placement | 0.111 s | 0.017 s | 0.052 s |

[Raw samples and workload hashes](../performance/data/jsonl/engine-baseline-2026-10-16.jsonl) record
the runner and executable paths. This is a local macOS arm64 baseline, not
a controlled CI threshold: Infera engine revision
`b08d850de8b11f7982f1054910df36a7ad9a3b89`, GHC 9.8.2, default Cabal library
profile `-O1`, executable `-O2`, RTS `-N1`; SWI-Prolog 10.0.2 and Scryer
0.10.0. The harness and checked fixtures were recorded with this roadmap
revision. Timings include startup, loading, solving and output;
warmups are validated and excluded from the samples. Re-record on the same
controlled runner/build configuration before judging a future regression.
Inference counts must also be checked before reporting an inference rate;
wall-clock timings alone do not establish one. The baseline reference engine
([Engine/Reference.hs](../../src/Infera/Engine/Reference.hs)) is a lazy list of solutions built from
Haskell closures:

* every call renames the clause (copies head and body), unifies into an
  immutable `IntMap`, deep-walks the arguments for indexing and sort checks,
  and threads the whole solver state (substitution, constraint store, tables,
  output log, dynamic facts) through each branch by value;
* recursion depth is nested Haskell evaluation, so there is no last-call
  optimisation and a hard bound of 100 000 nested activations
  (`maxResolutionDepth`);
* the search has no explicit stack or choice points, so a tracer, failure
  explanations (`:why`), step debugging and runtime errors with clause
  positions are all hard to add.

Step 1 addresses those architectural limits while preserving semantics and
the pure, lazy API. Step 2 focuses on dispatch and allocation costs after
that contract is established.

## Step 1: the abstract machine

### Implementation status

The local implementation now routes the existing public
[`Infera.Engine`](../../src/Infera/Engine.hs) API through
[`Infera.Machine.Control`](../../src/Infera/Machine/Control.hs).
`solveGoal`, `solveGoals`, `solveQuery`, `solveAll` and `runInfera` retain their
signatures and result types. The original resolver lives in
[`Infera.Engine.Reference`](../../src/Infera/Engine/Reference.hs) as the independent
parity oracle for both roadmap steps. No machine resolution path calls the
reference interpreter. **Step 1's historical local exit gates passed on
2026-10-16; Step 2 now has opt-in compiled activation, specialized head matching,
temporary register reuse, per-goal body allocation, compiled core control and
cut barriers, immutable predicate caches, resolved direct calls and dense operand
dispatch.**
The [Step 1 acceptance report](../performance/reports/engine-step1-acceptance-2026-10-16.md) records
that snapshot's checks and measurements. The
[Step 2 foundation report](../performance/reports/engine-step2-foundation-2026-10-16.md) records the
subsequent regression repair and initial compiler gate. The
[head/register report](../performance/reports/engine-step2-head-register-2026-10-16.md) covers later
specialized matching and allocation work.

The subsequent [application recheck](../performance/README.md#current-native-engine-recheck---2026-10-16)
found a material native regression: 16x16 ordinary minefield generation exceeded
30 seconds, versus 0.116s at the optimized reference stage. The regression is
fixed: accepted binding extensions avoid repeatedly validating old graphs,
call normalization retains shared heap graphs, and constrained calls stay on
the active driver. The larger setup/generation workload now has its own
validated runner and CI coverage. Current evidence and measurement scope are
in the [foundation report](../performance/reports/engine-step2-foundation-2026-10-16.md); historical
timings remain provenance, rather than current-source throughput acceptance.

[`Heap`](../../src/Infera/Machine/Heap.hs) supplies paged mutable cells, a trail,
occurs-checked unification, typed constant/functor interning and immutable
copy-on-write snapshots. The driver owns explicit task and choice stacks for
indexed clauses, conjunction, disjunction and scoped cuts. Shared
`Infera.Engine.Contracts` decisions keep signature selection, output/sort
validation and first-success commitment aligned with the reference. Matching
a head never commits a failing body, and an output-check error is not a
successful return. Declared `det`/`multi` failure obligations survive retries.
Native deferred cuts preserve foreign-marker ordering and committing barriers.

`start`/`resume` expose immutable suspended execution. The
[`Bridge`](../../src/Infera/Machine/Bridge.hs) preserves caller logical IDs,
cross-root sharing and the complete persistent solver state, including CLP
queues, output, tables and dynamic facts. Raw substitution links remain raw:
deep expansion can change shallow matching of control expressions. Every
choice and opaque scope owns a frozen heap paired with its saved branch state.
Restoring that snapshot replaces cells, trail, interning and frontiers together.
Allocation serials do not rewind on an in-place restore, and handles never
cross unrelated heaps or divergent resumptions without their matching snapshot.

Native scope frames implement `call`, `once`, `not`, if-then-else, `findall`,
general `minimize`, `forall`, `phrase`, `emit` and `phrase_from_file`. The
caller is parked with its own frozen heap and isolated from the child's cut
barrier. Streaming `call` retries restore the child's matching heap and rebase
its parked caller onto current scope buffers and success guards. Selected
states are synchronized back into the caller's restored heap. Negation and
failed conditions restore entry state; errors and exhaustion cannot establish
finite failure. `findall` retains the reference's template variable identities
and sharing, restores entry bindings/store/dynamic state, and concatenates
output from successful answers. `minimize` keeps the complete winning state,
retains the first on ties, and rejects incomplete or errored searches as proofs
of an optimum.

[`Builtins`](../../src/Infera/Machine/Builtins.hs) implements the remaining
ordinary builtins and dynamic-fact operations. Finite builtin algorithms
return native immutable result iterators; their tails are consumed only on
retry. Output logs and canonical dynamic facts remain persistent branch-local
values restored with the whole branch. Compact array logs or mutation journals
are future representation optimizations, not prerequisites for correctness.

[`Machine.CLP`](../../src/Infera/Machine/CLP.hs) connects heap binding transactions
to the complete persistent `Infera.CLP` store. Changed logical variables wake
the existing propagators, and propagated singleton bindings return to the heap.
Failure restores the heap transaction and prior variable/store version.
Constraint posting, ordinary labeling and `labeling [min Cost]` run under
native retry choices and incumbent scopes. The propagation algorithms remain
the existing persistent algorithms. Breadboard acceptance checks `rc`, `div`
and `tri` optima, byte-identical reporting, generated placements against
independent grid and exhaustive-labeling models, and the wider disconnected
case.

[`Machine.Table`](../../src/Infera/Machine/Table.hs) implements the general
variant fixedpoint and the existing narrowly proved delta path. Clause bodies
run through native driver callbacks; keys and answers contain immutable
canonical terms, never heap handles. A table fixedpoint is a native immutable
iterator boundary, rather than a producer task sharing the caller's active
heap. Producer work completes before its answer iterator yields; incomplete
ancestor dependencies, errors, exhaustion and truncation retain the reference's
ordering. Completed, incomplete and truncated caches remain distinct, including
when consumed with zero resolution fuel. Cutting or discarding an answer
iterator cannot complete an unfinished producer. Entries are branch-local;
there is no cross-rollback global table cache. Constrained calls and answers
fall back to plain native clause evaluation.

[`Tail`](../../src/Infera/Machine/Tail.hs) proves a closed first-order call graph
using native arithmetic, equality, guards and pure user predicates. This now
includes mutual recursion and prefix helpers. Reachable tabled, dynamic or
unsafe predicates, control/meta goals, effects, CLP posting and internal cut
markers are excluded from that source proof. The runtime additionally requires
an actual tail position, matching commit behavior, and no delayed declared
return obligation. Committing transfers require the original choice depth.
Pure noncommitting transfers can retire with parked internal retries because
each retry owns its original return frame, cut scope and frozen heap.
Undeclared calls may carry free or structured arguments; declared calls require
ground arguments and no required-success guard. Nonground declared output/sort
checks and `det`/`multi` obligations keep their frames.

Eligible transfers retire the caller return and cut owner and reuse its depth
budget. Allocation safe points at ordinary execution boundaries also reclaim
completed non-tail activations, including effectful calls and cut contexts.
They rebuild the active heap from query/caller roots,
remaining control terms, opaque-scope terms, CLP metadata and transitive raw
substitution links. Parked choices/scopes retain their own frozen pages, so
collection can proceed with live caller choices, opaque scopes, constraints,
completed tables, dynamic facts and output. Scope entry protects parent logical
roots needed after return. A raw graph relocation copies each reachable address
once, preserving shared suffixes and alias syntax. Undeclared return frames do
not retain arguments without delayed checks; declared return arguments remain
roots. Intern tables and trail history are rebuilt together;
the threshold starts at 1,024 cells and adapts to twice retained live size.
Fresh logical IDs remain monotone. Caller-owned entry IDs and reachable
identities remain observable; unreachable historical activation bindings are
retired from the returned substitution map. Explicit-fuel `startGoals` retains
its original nesting budget and disables tail reuse/collection. Other
ineligible calls retain the existing resolution-depth limit.

Loader metadata now maps predicate/clause ordinals and original body terms to
file/UTF-16 source spans, including qualified imports and expanded DCGs.
Ambiguous repeated goals and generated code fall back to their owning clause
span. The opt-in [`Trace`](../../src/Infera/Machine/Trace.hs) stream and
`resumeTraced` batches expose `Call`, `Exit`, `Redo`, `Fail`, `Cut` and
`Exception` events with logical frame chains and located errors. Table producer
callbacks also relay source locations and frames. Ordinary solving does not
retain events. The REPL supports `:trace query?`; the CLI accepts
`infera --trace FILE ["query?"]`. This is query tracing over immutable search
steps; interactive execution paused at every port remains separate future work.

Compiler-owned informational performance annotations continue to share the
CLI/LSP diagnostic path: `perf-non-tail-recursion`,
`perf-labeling-before-constraints`, `perf-unbounded-labeling` and
`perf-unselective-index`. Ten properties include 1,000 generated cases for
context/arity, finite bounds, indexing and precise locations. The editor can
hide performance hints independently and underlines resolved `unsafe` and
`dynamic` predicates through semantic-token settings.

The historical Step 1 validation passed 278 Haskell properties (20,698 property
test cases),
37 LSP tests, 20 benchmark-harness tests and CLI acceptance including trace mode. The expanded
checks cover ordered reference parity, independent models, complete metadata
rollback, immutable prefix/repeated/interleaved resumes, seeded table states,
mutual/helper tail calls, graph-sharing bounds, non-tail reclamation and
collection with live choices/scopes/CLP state.
`startMeasured` records execution high-water counters; normal solving avoids
that sampling. Active-heap counters do not count every parked frozen heap, so
fresh-process RTS residency and peak process RSS are separate acceptance data.

Earlier measurement files remain historical provenance, with their recorded
source fingerprints and build profiles:

* The [initial native CLP comparison](../performance/data/tsv/engine-native-clp-2026-10-16.tsv) and
  [initial tail/breadboard recheck](../performance/data/tsv/engine-tail-breadboard-2026-10-16.tsv) check
  exact breadboard answers; the small native cases were slower than the
  reference, without establishing a stable regression threshold.
* The [initial scalar tail samples](../performance/data/jsonl/engine-tail-2026-10-16.jsonl) record
  10k, 100k and 1m calls with bounded measured machine state and approximately
  81.5 MiB peak process RSS on the local GHC 9.8.2 `-O2` macOS arm64 build.
* The [free/structured tail samples](../performance/data/jsonl/engine-tail-structured-2026-10-16.jsonl)
  extend that early gate to shared structured inputs and free results, with
  roughly 85 MiB peak RSS at the same sizes. Those runs were single local
  samples, rather than repeated throughput estimates.
* The [breadboard recheck after structured tail reuse](../performance/data/tsv/engine-structured-tail-breadboard-2026-10-16.tsv)
  again validates all four cases and records native medians roughly 2–6 times
  the reference.

These files precede the public-engine switch and general live-checkpoint
collection. The historical Step 1 [residency samples](../performance/data/jsonl/engine-step1-tail-2026-10-16.jsonl)
record 28 checked fresh processes: repeated million-call mutual recursion,
live choices and findall, plus helpers, structured arguments, CLP, completed
tables and dynamic facts. Peak RSS stays between 126.8 and 127.9 MiB; measured
active heaps stay at or below 1,037 cells. The gate checks ordinary execution
and instrumented execution independently. Source fingerprinting and startup
are included in process maxima, so absolute RSS is not comparable with the
smaller historical fingerprint inputs.

The residency gate caught disabled trace metadata retaining retired callers,
lazy success-guard updates and repeated unchanged cut-barrier clamps. Strict
optional trace fields, eager owned-guard updates and no-op commits remove those
histories. The historical Step 1 [breadboard comparison](../performance/data/tsv/engine-step1-breadboard-2026-10-16.tsv)
validates exact answers and independent optima; native medians were roughly
1.3–4.6 times the reference on these small cases. No general throughput gain
is established. These costs remain the target of step 2.

The historical Step 1 [CLI matrix](../performance/data/jsonl/engine-step1-cli-2026-10-16.jsonl) validates reverse,
loop, Fibonacci and queens with one warmup and three timed runs each, using
an explicit 60-second per-process budget. Reverse's median is 32.551 seconds;
the earlier 30-second and 120-second timeouts are preserved in the acceptance
report's linked data. Allowing pure noncommitting tail retirement with parked
internal retries fixed growing active return stacks, but reverse still exceeded
the old 30-second budget in that snapshot. Fresh source/profile-matched samples
are needed to assess subsequent throughput changes.

Retaining old answers or continuations deliberately
retains their immutable pages; that caller-owned memory is distinct from
bounded execution with discarded predecessors. Growing live outputs also
require memory proportional to their size. Heap structures still use child
address lists rather than packed WAM cells, every binding is trailed, and
normalization/cut inspection can revisit large terms on every call. No general
throughput win is claimed. Those dispatch/allocation costs are the purpose of
step 2 after this exit gate passes.

### Data model

Terms stay the `Term` type of `Infera.Syntax` for everything outside the
machine (parser, printer, inference, answers).  Inside the machine, a running
term is a graph in a mutable heap:

```haskell
data Cell
  = Ref !Int             -- unbound variable: index of itself; bound: index of the value
  | Str !Int             -- pointer to a functor cell followed by its arguments
  | Fun !FunctorId !Int  -- functor table index and arity
  | Con !Constant        -- atom, integer, float, char, string (interned)
  | Lst !Int             -- cons cell: two consecutive cells
```

Step 1 uses boxed paged `Ref`, `Con` and `Structure` cells with opaque
generation-checked addresses. Structures retain child-address lists; the
packed functor/list representation above is an option for step 2.

* `Heap`: a growable unboxed/boxed `MutableArray` of cells in `ST s`, with a
  top-of-heap pointer `H`.
* `Trail`: a growable array of heap addresses and prior values, with `TR`.
  A write must be reversible if its cell survives the rollback checkpoint.
  Trail elision requires a proven allocation-age condition relative to every
  live rollback scope, including sub-search barriers. The absence of an
  ordinary clause choice point is not sufficient.
* Interned constants and functors: two tables mapping typed values and
  name/arity pairs to small ints. Strings and bignums live in the constant
  table. Scalar equality retains the reference semantics: floating-point
  interning uses bit keys, but unification compares values so signed zeros
  unify and NaN does not unify with itself.
* Loaded clauses remain immutable templates. `Term -> heap` instantiation
  happens per activation in step 1; repeated occurrences of a variable share
  one cell. Step 2 replaces template traversal with instructions. `heap ->
  Term` happens at answer and canonical-table boundaries.
* Unification retains the current occurs check: cyclic bindings fail rather
  than creating rational trees. Variable aliasing, fresh-variable isolation,
  residual constraints, exact integer arithmetic, term identity, and the
  shared numeric comparison rules (including NaN ordering) remain unchanged.

### Heap ownership and reclamation

Frame reuse and heap reclamation are separate requirements. Resetting `H` on
backtracking reclaims branch-local allocations, but a deterministic tail loop
has no backtrack to reclaim them. The machine therefore needs live-root
tracking and collection before it can claim bounded tail-loop residency.

Use a tracing collector at explicit allocation safe points. Its roots include
active frames and arguments, choice points and trail entries, CLP variable
references and pending propagators, active table producers/consumers, and
sub-search incumbents. Interned constant tables must either be query-local or
have an explicit lifetime policy. Frozen continuations own their immutable
pages; pages reachable only from discarded frames or continuations can be
released. A collector must preserve heap-age tests and rollback boundaries,
either through stable handles with separate allocation epochs or by updating
every address and age marker during relocation.

The million-iteration tail-loop gate measures peak live memory and maximum
frame depth as well as completion. After warmup, live memory must stay bounded
as the iteration count increases. Separately report retained memory when a
caller deliberately keeps previous answers or the head of a lazy stream;
that retention is owned by the caller, not evidence of a constant-space loop.

### Control

A continuation-passing design with explicit stacks, which is the standard way
to get Prolog control right without compilation:

```haskell
data Frame = Frame
  { frGoals   :: [Goal]       -- remaining goals of the clause body (heap terms)
  , frCutB    :: !Int         -- choice-point stack height when the clause was entered
  , frParent  :: !Int         -- continuation frame to return to
  , frPred    :: !PredKey     -- for tracing and error positions
  , frClause  :: !Int
  }

data ChoicePoint = ChoicePoint
  { cpGoals   :: [Goal]       -- goal list to resume with
  , cpFrame   :: !Int
  , cpAlts    :: !Alternatives -- remaining clauses (an index slice) or a builtin retry
  , cpTrail   :: !Int          -- TR at creation
  , cpHeap    :: !Int          -- H at creation
  , cpOutLen  :: !Int          -- output log length at creation
  , cpDynamic :: !Int          -- dynamic-fact journal length at creation
  , cpStore   :: !StoreVersion -- complete persistent CLP state and variable map
  , cpTables  :: !TableVersion -- branch-local table state and producer scope
  }
```

* **Call**: look up the predicate, select candidate clauses through the
  existing per-argument index (`candidateClauses`), push a choice point if more
  than one remains, rename the chosen clause onto the heap, unify the head,
  replace the current goals with the body.
* **Last-call optimisation**: a call in actual tail position can reuse the
  eligible caller's frame when their commit behavior and delayed obligations
  agree. Committing calls require their entry choice depth; noncommitting pure
  calls can leave independently frozen internal retries parked. This bounds
  frame growth for eligible tail calls; collection separately
  bounds dead heap growth. Removing `maxResolutionDepth` must preserve
  explicit resource-exhaustion reporting rather than causing a host crash.
* **Cut**: `!` pops the choice-point stack back to `frCutB` of its frame.
  Compatible foreign-owner markers remain observable through the public
  search API. `call`, `not`, `once`, `findall` and the if-then-else condition
  get a fresh cut barrier by recording the stack height.
* **Failure**: pop a choice point, unwind the trail to `cpTrail`, reset `H`,
  restore the complete CLP and branch-local table versions, truncate the
  output log and dynamic-fact journal, then resume `cpGoals`. Restore fresh-ID
  and retry bookkeeping consistently so no stale heap address can be reused.

### Pure, lazy query boundary

Use an immutable suspended checkpoint between externally observable search
steps. The driver has the shape `resume :: Checkpoint -> Step`, where `Step`
contains a compatible frozen `SearchItem` or completion and an optional
immutable next checkpoint. A `Found` step exports an immutable `SolverState`
with the same observable fields as today, not an `Answer` substituted for it.
`projectAnswer` can then project that state lazily through the existing API.
Adapters import/export compatible states for `solveGoal` and `solveGoals`.
Each call to `resume` runs mutation within its own `runST` scope.
No `STRef`, `MutableArray`, mutable table entry, or heap view escapes that
scope. `solveQuery` unfolds these pure transitions lazily.

Checkpoints use immutable heap pages and persistent control/store state, with
copy-on-write pages during a resume. Do not thaw an immutable page unsafely
while another answer or continuation can still reference it. The implementation
must measure freeze/copy costs; copying the entire live heap for every answer
would undermine the design and is not the intended default.

A returned `SolverState` owns immutable bindings, the complete CLP store,
output, table and dynamic-fact state; its public fields contain no live heap
addresses. An `Answer` projected from it and any issue metadata are immutable
as well. Advancing or discarding a continuation cannot change an earlier state
or answer. Internal sub-search snapshots follow the same ownership rule, even
when they are consumed eagerly inside one resume. Measure the cost of exporting
the compatible state as well as heap checkpointing.

Tests must cover taking only a prefix, retaining the first answer while forcing
the rest, consuming the same result twice in different orders, interleaving
independent queries, and discarding unfinished queries. Evaluation order must
not change bindings, output, dynamic state, or reported errors.

Declared `det`/`semidet` and eligible inferred `semidet` commits become "pop
choice points down to the barrier after the first successful body whose
declared output checks pass". Output-check errors before that success remain
in the search stream; they do not count as successful answers.
Declared `det`/`multi` failure checks look at whether any solution was
produced; `multi` retains all successes. A matching head is not a successful
solution: if its body fails, later clauses must still run. Conditional inferred
commits require the runtime groundness/switch conditions used by the current
engine. Keep declared contracts and advisory inference distinct.

### Sub-search scopes

Each construct owns a cut barrier and an entry checkpoint, but their state
retention differs. Port the reference engine's behaviour explicitly:

| Construct | State on return |
| --- | --- |
| `not Goal` | On successful negation, restore entry bindings, CLP, output and dynamic facts. A successful inner answer makes negation fail. Errors or exhaustion cannot be treated as ordinary finite failure. |
| `once Goal` | Retain the complete state of the first successful answer, including bindings, constraints, output and dynamic facts; discard its remaining alternatives. |
| `Condition -> Then ; Else` | Run `Then` from the first successful condition state. Run `Else` from entry state only after finite failure of the condition; errors/exhaustion do not select `Else`. A failing `Then` does not retry the condition or select `Else`. |
| `findall Template Goal List` | Freeze each collected template, preserving the reference's exact variable identity and sharing, including links to entry variables. The current evaluator dereferences templates without freshening their variable IDs; adding Prolog-style fresh copies is a separate semantics change. Restore entry bindings, CLP and dynamic facts, then unify `List`; concatenate output from successful collected answers in their order. Preserve the reference's error and exhaustion reporting. |
| `minimize Cost Goal` | Retain only the complete winning answer state, keeping the first on ties. An error or incomplete search cannot establish a minimum; losing candidates' bindings, output and dynamic facts do not escape. |

Preserve the order of issues encountered before a selected answer and the
incomplete-table dependency signals used by the current evaluator. Pruning
inner alternatives does not prune choices outside the construct's barrier.
`labeling [min Cost]` has its own retry and incumbent lifetime; an incumbent
must survive candidate rollback without leaking losing candidate state.

### Feature mapping

* **CLP(Z)** keeps the existing persistent propagation algorithms, including
  selective wakeups, batching and global all-different. `Machine.CLP` supplies
  tested heap binding/alias transactions and returns propagated bindings to
  stable logical variable roots. Every choice/scope retains the whole store:
  domains, constraints and their index, dependency sets, watched variables,
  pending propagators, dirty sets, next constraint ID and constraint count,
  together with the variable bridge. Collection traces those logical roots;
  restoring only domains and constraints would be incorrect.
* **Tabling** retains the general linear fixedpoint and eligible positive-rule
  delta algorithm in `Machine.Table`. Each clause body executes through a
  native callback with its own immutable search boundary. Producer state and
  dependency work remain local to that fixedpoint; the caller retains an
  immutable answer iterator under its native choice/scope. Canonical keys and
  answers contain no live heap handles. A producer's dependency, error or
  exhaustion signals cannot be turned into completion by cutting its result
  stream; completion and truncation remain distinct. Cross-rollback sharing
  is a future optimization, restricted to proven pure, complete entries whose
  keys include the program/dynamic version and all other relevant context.
  Effectful, incomplete, truncated or errored entries are not shared globally.
* **Output** retains the persistent reverse event log in `SolverState` and
  its length. Every saved branch owns that exact version, so retry restores
  branch output and each answer renders the events produced by that branch.
  An array log with a saved frontier remains a possible representation change.
* **Dynamic facts** retain canonical facts in assertion order, versioned by
  the persistent branch-local map. Native assert/retract operations update
  that version; restoring a choice or opaque entry restores the matching map.
  Active result iterators retain the fact snapshot selected when the call
  began. A compact mutation journal can replace this representation later
  without changing the branch-local update semantics.
* **Labeling and `minimize`** use native driver choices and opaque scopes.
  Label retries restore the complete candidate state; branch-and-bound
  labeling keeps the latest incumbent outside sibling retries. General
  `minimize` enumerates its native goal search, selects the complete winning
  state and retains the first on ties. Losing output/dynamic/store state
  cannot escape, and an incomplete or errored search establishes no optimum.
* **Errors** retain their existing kinds and public search ordering. Loader
  metadata maps qualified predicate/clause ordinals and original goal terms
  to file/UTF-16 spans. Unique goal sites get their own range; repeated equal
  goals and generated DCG/control code use the owning clause span. Native
  trace events carry these origins and logical frame chains, including table
  producer callbacks. Bytecode offsets will use this metadata in step 2;
  unavailable metadata is represented explicitly rather than a guessed site.
* **Tracing** exposes an opt-in immutable stream and per-resume event batches
  for `Call`, `Exit`, `Redo`, `Fail`, `Cut` and `Exception`. Discarding events
  preserves the public query stream. REPL `:trace query?` and CLI
  `infera --trace FILE ["query?"]` consume this hook. Events are emitted during
  full search steps; interactive pauses at individual ports, step debugging
  and `:why` remain future consumers.

### Module layout after step 1

```
src/Infera/Machine/Heap.hs      cells, trail, interning, Term <-> heap
src/Infera/Machine/Bridge.hs    logical IDs and complete reference-state adapters
src/Infera/Machine/CLP.hs       native binding transactions over persistent propagation
src/Infera/Machine/Control.hs   frames, choice points, driver loop, cut, LCO
src/Infera/Machine/Builtins.hs  the current builtin table, ported
src/Infera/Machine/Table.hs     native fixedpoints, scoped iterators, canonical answers
src/Infera/Machine/Tail.hs      closed first-order source and runtime eligibility gates
src/Infera/Machine/Trace.hs     opt-in immutable event/search stream
src/Infera/Machine/Trace/Types.hs source identities, frame chains and event values
src/Infera/Engine.hs            thin: solveQuery / answers / runInfera over the machine
src/Infera/Engine/Reference.hs  today's engine, retained through both steps and a parity release
```

### Milestones

1. **Implemented:** heap, trail, occurs-checked unification, typed constants,
   `Term` round trips and immutable checkpoint/resume ownership. Generated
   comparisons use `Infera.Unify`; retained/interleaved answers exercise the
   public lifetime contract.
2. **Implemented:** native indexed clauses, explicit control/backtracking,
   local and foreign cuts, contract-aware commitment, ordinary builtins and
   opaque sub-searches. The public `Infera.Engine` facade now selects this
   driver; `Infera.Engine.Reference` remains the parity oracle.
3. **Implemented and residency-validated:** closed first-order tail
   transfers include mutual recursion and prefix helpers. Active-heap
   reclamation coexists with separately owned frozen choices/scopes and live
   CLP/table/dynamic state. Required-success guards, nonground declared return
   checks, unsafe/dynamic/tabled callees, effects, control/meta goals and cut
   markers retain the conservative fallback. Eligible calls reuse their depth
   budget; explicit-fuel and other ineligible calls retain the original limit.
   The Step 1 acceptance snapshot's repeated million-call measurements confirm
   frame and process residency bounds, including ordinary execution without
   counters.
4. **Implemented:** CLP binding transactions, complete checkpoints, native
   labeling/minimum choices and breadboard acceptance against independent
   placement/propagation models.
5. **Implemented:** native variant fixedpoints and delta evaluation, immutable
   table iterators, branch-local dynamic/output versions, and first-success
   determinism guards. Generated comparisons and seeded complete/incomplete/
   truncated caches check ordered observations, rollback and fuel behavior.
6. **Implemented and CLI/trace-validated:** loader source maps,
   opt-in frame/event hook, REPL `:trace`, CLI `--trace`, and located errors
   with imported/DCG clause fallbacks. Table producers also relay native trace
  events. Interactive stepping is a separate future feature.
7. **Historical local gate passed:** the complete 278-property suite, 37 LSP
   tests, 20 harness tests, CLI/trace acceptance, exact breadboard comparisons and repeated
   that snapshot's residency measurements. Observable reference parity,
   immutable lazy answers and bounded eligible-tail residency pass. CI now
   builds the measurement runners and checks mutual/helper residency in fresh
   processes. Those counts and samples describe the Step 1 acceptance snapshot;
   the foundation report records checks for the subsequent changes. Retain the
   reference throughout step 2 and its parity release.

**Provisional performance target**: naive reverse at 2 million verified
inferences per second. This is an aspiration to revisit after profiling and
validated baselines, not a promised 10x improvement or a correctness gate.
The architectural gates are no fixed resolution-depth bound for eligible tail
loops and bounded live residency when callers do not retain old answers.

### Risks

* Heap-resident terms make `Term`-based code (answer projection, tabling
  canonicalisation, sort checks) copy more; keep those at the boundaries.
* Getting cut barriers right inside `call`/`findall`/tabling is where Prolog
  engines go wrong; the existing cut tests plus the correctness models are the
  guard.
* Scoped mutation adds freeze/copy costs; measure single-answer throughput,
  many-answer streaming and retained-prefix memory independently. Keep
  inference, parsing and propagation rules pure, and mutation ownership local.

## Step 2: bytecode

With the machine in place, compiling clauses targets two major remaining costs:
traversing clause templates to build head/body graphs per activation, and
general head matching where specialized instructions could avoid building the
whole head graph.

### Implementation status

The compiled path is opt-in through
`Infera.Machine.Control.ExecutionBackend` (`Interpreted` or `Bytecode`)
and the `startWithBackend`, `startMeasuredWithBackend`,
`startTracedWithBackend`, `startGoalsWithBackend` and
`solveQueryWithBackend` entry points. Public `Infera.Engine` calls and the
existing machine entry points still use the interpreted native driver.

[`Infera.Compile`](../../src/Infera/Compile.hs) emits a flat, postorder register
program for facts and clause bodies: `UseVariable`, `PutConstant`, `PutOwner`
and `PutCompound`. It also emits preorder `HeadVariable`, `HeadConstant` and
`HeadCompound` matching instructions. [`Machine.Bytecode`](../../src/Infera/Machine/Bytecode.hs)
reserves stable local roots and matches known caller shapes directly, avoiding
duplicate head constructors. When a caller target is free, it constructs only
that source subtree and uses ordinary occurs-checked heap unification.
Typed scalar comparison retains NaN's non-reflexive unification semantics.

Head writes accumulate in the original depth-first order, and
`Machine.CLP.unifyUsing` propagates them once after the entire structural
match succeeds. A later mismatch therefore suppresses earlier delayed CLP
errors exactly as whole-head unification does. An outer head checkpoint
rolls back roots, head nodes, trail and interning on rejection; each later
body materialization owns its allocation transaction.

Core body control now uses immutable `ControlCode` nodes for conjunction,
disjunction, cuts, `call`, `once`, negation, if-then-else and `findall`.
Conjunction schedules code children; disjunction parks its right code branch
in the existing frozen choice stack. Opaque nodes launch code through native
scope handling, preserving its error/output policies. If branches remain pure
code continuations until selected. `call` materializes callable/argument data
and uses the existing shallow callable expansion. Invocation plans and data
operands alone need heap graphs; untaken branches and core control wrappers remain
unallocated. No auxiliary predicate activation changes fresh IDs or fuel.

Compiled and interpreted cuts share one local/deferred-foreign cut helper and
the same choice barriers. Bare cuts are rewritten recursively, including
inside ordinary body data, through an activation-owner operand; head cuts stay
literal data. Literal if syntax and literal `$cut` owners are recognized from
raw source shape. A bound variable containing `->` or an integer owner retains
the native shallow runtime behavior. Trace mode reconstructs source terms
for events while preserving every syntactic control node and source location;
ordinary execution does not walk source templates.

Body construction begins after accepted head matching and propagation.
Variable/scalar registers share values using exact scalar bits, retaining
distinct NaN payloads and signed zero; compounds retain separate source slots.
The construction-register array is allocated lazily, separately from the head
target stack. A known-shape fact may need no head constructors or construction
registers, while its logical roots still reserve the same source IDs. Matched
caller compounds are never substituted for body templates, whose raw local
IDs remain observable. The driver now builds only the next reached body goal.
Its flat postorder plan uses direct local-variable operands and recycles scalar
and constructor registers after their last read. The immutable continuation
stores an activation base, remaining code and persistent suffix-live local-ID
sets, without heap addresses or mutable registers. Collection retains those
future locals and the current physical goal; materialization looks up the
existing raw roots after relocation and never recreates retired locals. The
final goal removes the continuation before dispatch so tail reuse still sees
the return boundary. The source-local ID range is reserved up front; full
argument/environment register allocation and lazy root reservation are still
future work.

Known ordinary user calls use `DirectRun`; builtins retain their existing
dispatch precedence. The driver retains clause selection, contracts, success
guards, tail eligibility and backtracking. VM head/allocation/avoidance/register
counters distinguish accepted-head work from reached body materializations;
rejected heads return no activation statistics. Normal execution performs no
instruction-statistic writes.

Malformed local IDs or uncallable heads retain the interpreted fallback.
Dynamic/noncallable leaves and malformed control arities compile as generic
invocations whose native runtime checks decide their behavior. Less-common
meta/DCG operations (`forall`, `minimize`, `phrase`, `emit`, file phrases) still
use their native handler through invocation plans. Original body templates
remain source metadata for trace locations. Registers
are private to activation; immutable checkpoints retain heap handles with their
matching branch snapshots and the exact program/code version.

Code now belongs to immutable predicate versions. Loading attaches lazy
source-only plans; the first selected clause forces its plan and subsequent
queries/producers share it. An exact source witness protects public record
edits, including local counts, constructor distinctions and floating-point
bits. Each query memoizes the selected result, including unsupported clauses,
so retries and opaque returns need no repeated witness walk. Unchanged clause
entries survive normal incremental edits; retained checkpoints keep their
original program and plans. Direct `predClauses` edits safely recompile stale
entries once per query; rebuilding `predClauseCache` restores cross-query reuse.
Table producers retain their existing head/template path, with their native
body callbacks selecting the requested backend. The historical
[foundation report](../performance/reports/engine-step2-foundation-2026-10-16.md) distinguishes this
initial slice from the remaining WAM-style design. Its initial validated
samples established compiled execution and parity without establishing a
throughput gain over the interpreted driver. The
[head/register report](../performance/reports/engine-step2-head-register-2026-10-16.md) records
subsequent implementation and validation. The
[lifetime report](../performance/reports/engine-step2-lifetimes-2026-10-16.md) records incremental body
construction, temporary register reuse and their acceptance results. The
[control report](../performance/reports/engine-step2-control-2026-10-16.md) records compiled control
continuations, cut barriers and the next default-backend gates. The
[cache/dispatch report](../performance/reports/engine-step2-cache-2026-10-16.md) records the subsequent
implementation, cold/warm measurements and remaining migration gates.
The [operand report](../performance/reports/engine-step2-operands-2026-10-16.md) records subsequent
dense local layouts, simple-plan fast paths, transaction-owned node allocation
and guarded invocation fusion.

### Planned instruction set (WAM-lite)

Registers `A1..An` for arguments, `X` temporaries, `Y` permanent variables in
an environment frame.

```
# head unification (get)        # body argument construction (put)
get_constant C, Ai              put_constant C, Ai
get_variable Vn, Ai             put_variable Vn, Ai
get_value Vn, Ai                put_value Vn, Ai
get_structure F/N, Ai           put_structure F/N, Ai
get_list Ai                     put_list Ai
unify_variable Vn / unify_value Vn / unify_constant C / unify_void N

# control                       # clause selection
allocate N / deallocate         try_me_else L / retry_me_else L / trust_me
call P/N, K / execute P/N       switch_on_term Lv, Lc, Ll, Ls
proceed                         switch_on_constant / switch_on_structure
cut / cut_to Y
builtin B, N                    # calls into the builtin table
```

The index built today for every argument position becomes
`switch_on_*` instructions on the first argument plus a filtered clause list
for the others (keeping the current behaviour that any bound argument prunes).

### Compiler

The full compiler will classify variables as temporary or permanent, assign
argument/environment registers, emit `get_*` for the head,
`put_*` and `call`/`execute` for the body, and surround bodies with permanent
variables with `allocate`/`deallocate`. Environment trimming follows the last
use of each permanent variable. Core control constructs (`,`, `;`, `->`, `not`,
`once`, `findall`) now compile to code continuations with the existing cut
barriers, preserving fresh IDs, resolution fuel and trace frames.
DCG rules are already plain clauses by the time they reach the compiler.

Declarations and inference feed the compiler subject to runtime guards. A
declared `det`/`semidet` or eligible inferred `semidet` call commits remaining
alternatives only after a successful body and declared output checks;
`trust_me` must not discard later clauses merely because a head matched.
Declared `det`/`multi` inserts the zero-success check. Conditional inferred commits
retain the current switch/groundness tests, including calls through aliases
and variable arguments. Preserve errors encountered before the first valid
success. Test a first matching clause whose body fails, an output-check error,
and a later clause that succeeds.

Inferred `<=` positions are advisory and do not prove that a variable is
ground or younger than a rollback checkpoint. They cannot justify trail
elision. Skip a trail operation only with an allocation-age proof, or a checked
runtime guard proving no surviving state needs the prior cell value. A future
compiler groundness proof must cover actual call sites and preserve fallback
behaviour; inference alone is not that proof.

### Runtime

The machine from step 1 gains an instruction loop; frames become environments
with `Y` registers; builtins, CLP, tabling, output and dynamic facts are
unchanged because they already sit behind the machine interface. Source maps
and trace events must survive instruction fusion and compiled continuations.
Predicate code caches depend only on exact source syntax. Runtime dispatch,
table/index flags and tail proofs belong to the exact immutable program
attached to a query, so metadata and REPL edits cannot reuse stale proofs.
Known ordinary calls carry their resolved predicate and metadata through
dispatch; a query-wide dynamic-name set preserves cross-arity declarations
without scanning the program on every compiled call. Builtins retain
precedence and dynamic calls consult branch-local facts. Future dependent
specialisations must invalidate when their assumptions change; syntax-only
plans need no invalidation for unrelated signatures, files or source maps.

### Making bytecode the public default

Bytecode is the intended eventual default. The public facade remains on
`Interpreted` while that migration is prepared. Predicate caches and resolved
dispatch remove repeated whole-program compilation and per-call dynamic-name
scans. Dense local operands remove per-leaf local maps, layouts of up to four
locals use bounded list reads, simple plans avoid
temporary arrays, and one materializer transaction owns all reached node
allocations. Normal invocation fusion avoids a redundant task round trip below
collection thresholds; tracing/measurement/collection keep their boundaries.
Generic native services can remain shared behind compiled
instructions; changing the default does not require duplicating CLP, tables
or dynamic-fact algorithms.

Before switching, require the complete generated/API/stdlib suite and exact
source traces under both backends, cross-platform CI, real breadboard/minefield
acceptance, retained-checkpoint and million-iteration residency gates, and
checked serial cold/warm timings without material representative regressions.
The user-selected external target is roughly **2× or better than either SWI
or Scryer across representative, answer-checked workloads**. Compare explicit
bytecode loaded execution separately from CLI startup; require a valid result
and usable timing in each comparison, and retain workload gaps explicitly.
Then route public `Infera.Engine` entry points to bytecode, retain explicit
`Interpreted` selection for differential checks and troubleshooting, and run
the full default-facing CLI/editor suite again. The reference remains an
oracle through the planned parity release.

The cache/dispatch recheck removed the unused-predicate scaling regression.
Operand dispatch now precomputes dense local layouts while preserving source
logical IDs, strict branch-owned root lookup, error ordering and private
construction arrays. Opaque scopes preserve the same protected-ID union as a
lazy set, avoiding repeated list/set/list conversion without forcing work for
short searches that never collect. A strict outer wrapper extracts only the
parent set and immutable bindings before deferring that union, avoiding a
selector closure over the entire parent driver. The operand report separates
matched cold queries and fresh-state warm batches, including intermediate
refinements and sample variation. Profile remaining regressions before
builtin/argument-register specialisation; a default switch remains a separate
validated migration. The operand recheck recorded warm-control and RC/wide
breadboard regressions. The subsequent typed builtin report records the new
paired comparison: control and wide improve locally, but the minefield sanity
case regresses against baseline. The representative performance gate remains
open despite passing local correctness.

### Next performance work

Prioritize remaining builtin/operand round trips over more predicate-cache
work: the latest probes report zero predicate-cache misses. These are
source-grounded candidates, not established causes of the measured regressions.
Profile normal execution on a controlled runner before claiming a speedup.

1. **Typed builtin arguments implemented for 18 fixed arithmetic/CLP calls.**
   [The typed builtin report](../performance/reports/engine-step2-builtin-operands-2026-10-17.md) records
   shared multi-root argument plans, direct heap unification and scalar-result
   `is`, with the source invocation retained for tracing and malformed calls.
   Each operation owns argument allocations and the CLP/heap result together.
   Other typed builtins still export raw argument terms for the existing
   arithmetic/CLP helpers. Expression opcodes and additional builtin coverage
   remain later profiling candidates. Dynamic goals, malformed shapes and
   unsupported cases retain generic dispatch. Builtin precedence, shallow walks,
   exact error order, fuel, rollback and source traces remain invariants.
   New counters identify typed calls and omitted wrappers separately from the
   generic invocation and traced fallback paths.
2. **Opaque controls and tail transfer implemented.**
   [The opaque control report](../performance/reports/engine-step2-opaque-controls-2026-10-17.md) records
   split arithmetic/once/negation/conditional benchmarks and matched measurements.
   Successful once/conditional/emit scopes keep the current child's heap and
   bindings when a monotone heap epoch proves the parent's prefix addresses
   survived. Restores, relocating collections and traces retain state replay;
   earlier minimum-search results always use the existing restore/replay path.
   A closed proof admits only pure, fully checked control trees for frame
   retirement, including every alternative and reachable definition. Historical
   fuel-refund eligibility remains a separate, unchanged proof, so newly retired
   frames still consume the existing logical resolution budget. Generated tests
   retain complete stores, rollback, contracts, cuts, checkpoints and traces.
3. **Compiled arithmetic expression plans.** The checked external arithmetic
   loop is substantially slower than Scryer even without opaque controls.
   Typed builtins still construct an expression on the heap, export it to
   syntax and evaluate through the persistent substitution. Compile supported
   ground-integer expressions for `is` and ordinary comparisons to numeric
   plans, retaining generic fallback for blocked variables, malformed inputs,
   unsupported operations and traces. Preserve exact arithmetic/error order,
   transactional rollback and native unification/CLP synchronization. Profile
   callable export, fresh activation variables and substitution mirroring too;
   this is a bounded next candidate, not evidence that one change closes the
   external gap.
4. **CLP change tracking.** Separate posting, fixed labeling and full optimum
   search on all four breadboard cases. If profiles justify it, return actual
   newly bound IDs from trusted internal CLP operations instead of deriving
   differences from whole substitutions, and avoid replacing dependency
   registrations when a reduced constraint's variable membership is unchanged.
   Keep public arbitrary-callback synchronization strict and retain search order
   and labeling heuristics during this change.

Each phase needs generated ordered-answer/error/residual/output parity,
retained/interleaved snapshots, exact traces and strict root ownership, plus
real minefield/breadboard acceptance and residency checks. Record paired CPU
and wall time for both cold queries and fresh-state warm batches, retaining
Reference and Interpreted as controls. The current three-sample variation does
not establish a default-ready speedup; declare the material-regression tolerance
before the next controlled comparison.

### Milestones

1. **In progress:** compiled activation, specialized head matching, per-goal
   body construction, temporary register reuse and direct ordinary user calls for
   facts/first-order rules, with opt-in backend selection and interpreter
   fallback. Generated tests compare both native backends with Reference,
   including whole-head CLP error order, raw local IDs, contracts, source frames
   and immutable repeated/interleaved resumes. Table producer heads retain
   their template path. Broader stdlib acceptance and the remaining compiled
   paths must pass before declaring the full first-order milestone complete.
2. **Core control implemented:** direct code continuations for conjunction,
   alternatives, cuts, `call`, `once`, negation, conditionals and `findall`,
   using native choices/scopes/contracts. Less-common meta/DCG handlers and
   dynamically expanded call targets retain native dispatch. Full acceptance
   and performance evidence are recorded in the control report.
3. **Predicate caching and resolved dispatch implemented:** lazy immutable
   clause plans, exact edit witnesses, per-query runtime metadata and direct
   resolved calls. Remaining: indexing instructions; full argument/environment
   registers and trimming; LCO in `execute`; remaining invocation/builtin costs.
4. Determinism-directed code generation from declarations and inference.
5. Full differential and API-lifetime suite against both the step 1 machine
   and reference; validated benchmarks on a controlled runner. Retire the
   reference only after step 2 has passed a full parity release, retaining
   independent correctness models thereafter.

**Provisional performance target**: 8 million verified inferences per second
on naive reverse, to be revised against validated baselines and profiling.
Make no relative-speed claim against another engine without checked equivalent
workloads and repeated measurements. The step 1 debugger and tracer must still
work through the instruction loop's event hook.

## Explicitly not planned

* A JIT: Prolog JITs have a poor record, GHC is an awkward host, and the
  workloads this language targets are search and constraint bound, where
  indexing, tabling and propagation strength dominate instruction dispatch.
* Changing the surface language: every example and test in the repository is
  the acceptance suite for both steps.

## Validation throughout

* The established engine properties (including correctness models and the
  signature golden file), plus the 12 heap properties, 14 control/bridge
  properties, nine native sub-search properties and subsequent
  machine/compiler properties, must pass
  against each engine. Keep generated comparisons with independent models as
  well as the reference; agreement between two engines is not a proof.
* Compare ordered answers, duplicates, residual constraints, output, error
  kind/order and exhaustion between engines. Compare shipped examples' output
  byte for byte. Equivalent fresh-variable names may be normalised without
  hiding variable-sharing differences.
* Generated cases cover occurs checks, aliasing, numeric edge cases, nested
  cut/sub-search scopes, first-body failure under det/semidet, CLP rollback,
  table completion/truncation and dynamic-fact visibility. API tests cover
  partial/interleaved consumption and immutable earlier answers.
* `test/cli.py` exercises the binary end to end.
* `bench/run.sh` checks process success and expected results for naive reverse,
  the counting loop, untabled Fibonacci and 8 queens before reporting timed
  samples. It supports warmups, repeated runs, a timeout, median reporting and
  machine-readable results. Failed execution, wrong answers and timeouts must
  fail the command, not appear as fast measurements. Optional SWI-Prolog and
  Scryer runs use equivalent checked workloads.
  For an Infera-only baseline, run:

  ```sh
  bench/run.sh --engine infera --runs 3 --warmup 1 --timeout 30 --json
  ```

  Without `--engine`, the harness automatically selects available engines
  from Infera, SWI-Prolog and Scryer. The four validated cases run by default.
* Record the engine/build revision, compiler options, workload parameters,
  runner and measurement scope with a new baseline. Keep `test/bench.py` for
  its separate minefield, graph and breadboard workloads; validate answers and
  optima there before using their times. SEND+MORE=MONEY currently lives in
  `examples/v2_clp.nprolog`; adding a validated benchmark case for it is a
  separate future gate. Measure tail-loop live residency separately from the
  CLI timing harness.
* The optional `machine-breadboard` benchmark compares the experimental machine
  and reference using the same already-loaded checked program. It validates
  the three shipped circuits and wide disconnected example against physical
  placement and independent optimum checks before reporting each sample:

  ```sh
  cabal bench machine-breadboard --offline --enable-optimization=2 --benchmark-options='+RTS -T -RTS'
  ```

  One warmup and three measured runs per engine/case use a 30-second timeout.
  The runner records wall/CPU samples, source fingerprint, compiler/platform
  and build scope. Timings include execution, answer projection and validation;
  they exclude source parsing, loading and inference, so they cannot be compared
  directly with CLI harness timings. It uses distinct unused fresh-variable
  bases to avoid sharing evaluated pure results between samples. Failed,
  exhausted or invalid runs do not produce a timing row. These measurements
  have no CI timing threshold and do not establish bounded live residency.
* The separate `machine-tail` runner verifies one checked loop per fresh
  process and drains its continuation. Run both modes at 10k, 100k and 1m
  iterations; the measured mode records machine counts, and the ordinary mode
  checks that counter sampling did not hide retention:

  ```sh
  cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='1000000 +RTS -T -s -RTS'
  cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='1000000 --unmeasured +RTS -T -s -RTS'
  cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='1000000 --case result --unmeasured +RTS -T -s -RTS'
  cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='1000000 --case structured --unmeasured +RTS -T -s -RTS'
  ```

  The default `ground` case preserves the original scalar fixture; `result`
  transfers a free output, and `structured` transfers a compound with a shared
  free leaf. Each verifies its exact projected answer. JSON distinguishes
  cumulative allocation, process maximum live residency
  and current final live memory. The recorded local ordinary runs also include
  whole-process peak RSS/footprint from macOS `/usr/bin/time -l`. Startup and
  source fingerprinting are included in process memory maxima. A retained old
  checkpoint owns its old pages; test that case independently of the
  unretained-loop memory measurement. General tail calls and collection with
  surviving choices/scopes are covered by the current residency gate:

  ```sh
  cabal build bench:machine-tail --offline --enable-optimization=2
  python3 bench/check-tail-memory.py "$(cabal list-bin bench:machine-tail --enable-optimization=2)" --output tail-memory.jsonl
  ```

  The full matrix validates all answers and requires peak RSS and RTS maximum
  live bytes to remain within 1.5 times the prefix-process maxima. `--quick`
  retains mutual recursion and prefix helpers for ordinary CI. The check caught
  real history-retention bugs despite bounded active-machine counters.
* Ordinary CI runs correctness, benchmark-harness failure and relative memory
  checks. Elapsed-time regression thresholds belong on a controlled runner with repeated
  measurements and recorded variance, not normal shared CI. Choose thresholds
  after establishing a stable validated baseline; the former 20% threshold is
  not an acceptance requirement yet.
