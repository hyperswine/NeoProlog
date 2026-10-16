# Engine roadmap: from a lazy-list resolver to an abstract machine

This is the plan for replacing the resolution core of Infera in two steps:

1. **An explicit abstract machine** (`Infera.Machine`): mutable bindings with a
   trail, an explicit goal stack and choice-point stack, last-call
   optimisation, bounded live memory for deterministic tail calls, and hooks
   for tracing. Same source language and observable query behaviour.
2. **Bytecode compilation** (`Infera.Compile`, `Infera.VM`): clauses compiled
   at load time to a small WAM-style instruction set executed by the machine
   from step 1.

Everything above the engine keeps its public behaviour: the parser,
declarations and inference
([Infer.hs](../src/Infera/Infer.hs)), the purity gate, the CLP(Z) store's
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

[Raw samples and workload hashes](engine-baseline-2026-10-16.jsonl) record
the runner and executable paths. This is a local macOS arm64 baseline, not
a controlled CI threshold: Infera engine revision
`b08d850de8b11f7982f1054910df36a7ad9a3b89`, GHC 9.8.2, default Cabal library
profile `-O1`, executable `-O2`, RTS `-N1`; SWI-Prolog 10.0.2 and Scryer
0.10.0. The harness and checked fixtures were recorded with this roadmap
revision. Timings include startup, loading, solving and output;
warmups are validated and excluded from the samples. Re-record on the same
controlled runner/build configuration before judging a future regression.
Inference counts must also be checked before reporting an inference rate;
wall-clock timings alone do not establish one. The current engine
([Engine.hs](../src/Infera/Engine.hs)) is a lazy list of solutions built from
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

The first isolated foundation is in
[`Infera.Machine.Heap`](../src/Infera/Machine/Heap.hs): paged mutable cells and
trail, reversible occurs-checked unification, activation-local variable
environments, typed constant/functor interning, and immutable copy-on-write
heap snapshots. Twelve heap properties include 1,500 generated comparisons
with `Infera.Unify`, plus fixed failure, aliasing, scalar, rollback and
page-boundary cases.

This starts milestone 1. The production resolver still uses `Infera.Engine`;
the search driver, compatible frozen `SolverState` exports, control stack,
CLP/table adapters and collector remain to be implemented. Initial structures
hold child-address lists rather than packed WAM cells, and every binding is
trailed. The opaque layout can change after profiling. No query-speed or
bounded-residency improvement is claimed by this isolated layer.

Heap addresses, activation environments and rollback marks belong to one
branch. They may accompany the matching frozen snapshot, but must not cross
independent heaps or divergent resumed branches. Allocation generations reject
discarded addresses within a branch; they are not global heap identities.
`ST` contains mutable pages, but the address type alone does not enforce this
ownership rule. The control driver must preserve it explicitly.

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
* **Last-call optimisation**: when the current frame has no remaining goals
  after the call and no choice point was created since it was entered, the
  callee can reuse the frame if no surviving alternative or sub-search needs
  it. This bounds frame growth for eligible tail calls; collection separately
  bounds dead heap growth. Removing `maxResolutionDepth` must preserve
  explicit resource-exhaustion reporting rather than causing a host crash.
* **Cut**: `!` pops the choice-point stack back to `frCutB` of its frame.  No
  more markers in the answer stream; `call`, `not`, `once`, `findall` and the
  if-then-else condition get a fresh cut barrier by recording the stack height.
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

* **CLP(Z)**. Preserve the current propagation algorithms, including selective
  wakeups, batching and global all-different. Introduce a tested binding
  interface (`walk`, `bind`, `freshVar`) rather than assuming today's pure
  substitution functions already operate on the heap. Give constrained
  variables stable logical IDs with a reversible logical-ID/heap-handle map;
  aliasing, copying and collection must update that bridge consistently.
  Every checkpoint records the whole persistent store version: domains,
  constraints and their index, dependency sets, watched variables, pending
  propagators, dirty-variable sets, next constraint ID and constraint count,
  plus the variable map. Restoring only domains and constraints is incorrect.
  Binding/aliasing a watched variable wakes the relevant dependencies using
  the same semantics as the current store. Keep the pure-store adapter until
  generated rollback and propagation comparisons pass.
* **Tabling** preserves both the general linear fixpoint evaluator and the
  incremental path for eligible positive rules. Canonical answers and table
  keys contain immutable terms, never live heap addresses. Incomplete
  producers, consumers, dependency signals and retry work belong to an
  explicit sub-search scope and are rolled back or cancelled with that scope;
  they cannot become completed merely because a cut, `once`, error or
  resource limit stopped their producer. Completion and truncation remain
  distinct. Start with the current branch-local table retention. Sharing
  completed tables across rollback is a later optimisation allowed only for
  proven pure, complete entries with keys including the program/dynamic-fact
  version and any other relevant context. Effectful, incomplete, truncated or
  errored entries are never shared through that cache.
* **Output** keeps today's semantics (each answer prints exactly the output of
  the branch that produced it): the log is a growable array truncated on
  backtracking through the choice point's `cpOutLen`.
* **Dynamic facts** become a journal of assert/retract operations truncated on
  backtracking, so the logical update view per branch is unchanged. Active
  calls retain the fact-version snapshot used when clause selection began.
* **Labeling and `minimize`** are rewritten as choice points with builtin
  alternatives (`retry` entries) instead of eager lists.
* **Errors**: preserve source spans through parsing, module loading, clause
  expansion and compilation. Stable clause/goal IDs map frames and bytecode
  offsets to original file spans; synthetic DCG/control code retains an
  origin mapping. Predicate and clause numbers alone cannot recover positions
  from today's loaded program. Add loader metadata before promising located
  errors, and retain the existing error kind and ordering.
* **Tracing**: the machine exposes an event hook (`Call`, `Exit`, `Redo`,
  `Fail`, `Cut`) with the current frame chain. A future REPL `:trace` command
  and CLI trace option are the first consumers; define their CLI syntax before
  documenting usage. The current CLI accepts file arguments and has no
  `infera run --trace` command. A future `:why` can replay the last failing
  branch.

### Module layout after step 1

```
src/Infera/Machine/Heap.hs      cells, trail, interning, Term <-> heap
src/Infera/Machine/Control.hs   frames, choice points, driver loop, cut, LCO
src/Infera/Machine/Builtins.hs  the current builtin table, ported
src/Infera/Machine/Table.hs     scoped tabling and immutable canonical answers
src/Infera/Engine.hs            thin: solveQuery / answers / runInfera over the machine
src/Infera/Engine/Reference.hs  today's engine, retained through both steps and a parity release
```

### Milestones

1. Heap, trail, unification, `Term` round trip; property tests against
   `Infera.Unify` (same success/failure, occurs check and variable sharing).
   Implement the immutable checkpoint/resume boundary and answer-lifetime
   tests before exposing the machine through the public API.
2. Control: facts and rules, backtracking, cut, if-then-else, negation,
   `findall`, `once`; the whole existing suite passes against the new engine
   with CLP and tabling still routed through adapters.
3. LCO, root tracking and reclamation; `loop 1000000` runs without growing
   frame depth or unbounded live heap. Remove the resolution-depth bound only
   after resource errors and residency measurements pass.
4. CLP binding adapter and complete checkpoints; the CLP examples,
   propagation models, aliasing and generated rollback comparisons pass.
5. Scoped tabling; dynamic fact versions; output log; first-success
   determinism commits; generated sub-search and error/exhaustion comparisons.
6. Loader source spans, tracing hook, `:trace`, located runtime errors.
7. Step 1 exit gate: full observable parity with the reference, immutable
   lazy answers, bounded tail-loop live memory, and validated repeated
   measurements. Retain the reference for step 2 and its parity release.

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

Once the machine exists, compiling clauses removes the two remaining costs:
building clause bodies on the heap per activation, and interpreting head
unification one `Term` node at a time.

### Instruction set (WAM-lite)

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

`Infera.Compile` turns a `Clause` into instructions: classify variables as
temporary or permanent, assign registers, emit `get_*` for the head,
`put_*` and `call`/`execute` for the body, `allocate`/`deallocate` around
bodies with permanent variables, environment trimming after the last use of
each permanent variable.  Control constructs (`,`, `;`, `->`, `not`, `once`,
`findall`) compile to auxiliary predicates with cut barriers, the standard
transformation.  DCG rules are already plain clauses by the time they reach
the compiler.

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
and trace events must survive instruction fusion and auxiliary predicates.
Bytecode is produced at load time and cached per predicate. REPL clause
additions recompile the changed predicate and invalidate any dependent
specialisations or table caches whose proof depended on the old program.

### Milestones

1. Compiler and VM for facts and first-order rules (no control constructs);
   differential test against the step 1 machine on the stdlib.
2. Control constructs and cut barriers; the full suite.
3. Indexing instructions; environment trimming; LCO in `execute`.
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

* The established 109 Hedgehog properties (including correctness models and the
  signature golden file), plus the 12 heap properties and subsequent
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
* Ordinary CI runs correctness checks and benchmark-harness failure tests.
  Numeric regression thresholds belong on a controlled runner with repeated
  measurements and recorded variance, not normal shared CI. Choose thresholds
  after establishing a stable validated baseline; the former 20% threshold is
  not an acceptance requirement yet.
