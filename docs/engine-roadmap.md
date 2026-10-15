# Engine roadmap: from a lazy-list resolver to an abstract machine

This is the plan for replacing the resolution core of Infera in two steps:

1. **An explicit abstract machine** (`Infera.Machine`): mutable bindings with a
   trail, an explicit goal stack and choice-point stack, last-call
   optimisation, and hooks for tracing.  Same source language, same answers.
2. **Bytecode compilation** (`Infera.Compile`, `Infera.VM`): clauses compiled
   at load time to a small WAM-style instruction set executed by the machine
   from step 1.

Everything above the engine stays: the parser, declarations and inference
([Infer.hs](../src/Infera/Infer.hs)), the purity gate, the CLP(Z) store's
propagation logic, DCG translation, the REPL, `infera check`, the LSP and the
test suite.  The engine's public surface
(`solveQuery`, `solveAll`, `runInfera`, `Answer`, `QuerySummary`,
`OutputEvent`) is kept so that nothing downstream changes.

## Why

Measured on the same programs (see the README's validation section for how
to reproduce):

| workload | today | SWI-Prolog | Scryer |
| --- | --- | --- | --- |
| naive reverse, 1.5M inferences | 6.6 s | 0.12 s | 0.20 s |
| counting loop to 90 000 | 0.30 s | 0.01 s | 0.05 s |
| `fib 25`, untabled | 0.46 s | 0.05 s | 0.07 s |

About 225 000 inferences per second against 10 to 15 million.  Speed is not
the first problem, though.  The current engine
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

Those three are what step 1 fixes.  Step 2 is purely about speed.

## Step 1: the abstract machine

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
* `Trail`: a growable array of heap addresses whose bindings must be undone on
  backtracking, with `TR`.  Binding a variable records its address when it is
  older than the current choice point (the usual condition), so forward
  execution without choice points leaves no trail.
* Interned constants and functors: two tables mapping names to small ints, so
  unification compares ints.  Strings and bignums live in the constant table.
* Conversion `Term -> heap` happens once per clause at load (step 1 keeps
  clause bodies as terms and builds them on the heap per activation; step 2
  compiles them away) and `heap -> Term` when projecting answers.

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
  }
```

* **Call**: look up the predicate, select candidate clauses through the
  existing per-argument index (`candidateClauses`), push a choice point if more
  than one remains, rename the chosen clause onto the heap, unify the head,
  replace the current goals with the body.
* **Last-call optimisation**: when the current frame has no remaining goals
  after the call and no choice point was created since it was entered, the
  callee reuses the frame.  This is what removes the depth bound; deep
  recursion becomes heap growth, bounded only by memory.
* **Cut**: `!` pops the choice-point stack back to `frCutB` of its frame.  No
  more markers in the answer stream; `call`, `not`, `once`, `findall` and the
  if-then-else condition get a fresh cut barrier by recording the stack height.
* **If-then-else, negation, once**: run the condition as a sub-computation with
  a barrier; on first success pop to the barrier and continue with the branch.
* **Failure**: pop a choice point, unwind the trail to `cpTrail`, reset `H`,
  truncate the output log and dynamic-fact journal, resume `cpGoals`.
* **Answers** are produced by a driver loop that resumes the machine for the
  next solution; `solveQuery` wraps it as the lazy list the rest of the
  system expects, so laziness is preserved at the API without being used
  inside the engine.

Determinism commits (declared or inferred `semidet`) become "pop choice
points down to the barrier after the first solution", exactly like cut, and
`det` failure checks look at whether any solution was produced.

### Feature mapping

* **CLP(Z)**.  The store keeps its domains and constraints, but its
  substitution is the machine's binding array.  Propagation is already written
  against `walk`/`unify`; it is parameterised over a small record
  (`walk`, `bind`, `freshVar`) so the same code runs over the heap.  Domains and
  the constraint list are trailed: a choice point records the store version,
  and the store becomes a persistent structure (as now) referenced from a
  mutable cell, which is the cheapest correct option.  Attributed variables
  (binding a constrained variable wakes propagation) are implemented by
  checking a per-variable "watched" bit at bind time, replacing today's
  `isConstrained` scan.
* **Tabling** keeps the linear fixpoint algorithm.  Tables move to a mutable
  map owned by the machine; the "consumed incomplete table" signal becomes a
  flag on the table entry rather than an item in the answer stream; answers
  stay canonical terms.  Nothing in the inference of what to table changes.
* **Output** keeps today's semantics (each answer prints exactly the output of
  the branch that produced it): the log is a growable array truncated on
  backtracking through the choice point's `cpOutLen`.
* **Dynamic facts** become a journal of assert/retract operations truncated on
  backtracking, so the logical update view per branch is unchanged.
* **Labeling and `minimize`** are rewritten as choice points with builtin
  alternatives (`retry` entries) instead of eager lists.
* **Errors**: a `BranchError` carries the frame's predicate and clause number,
  which gives runtime errors a source position for the first time.
* **Tracing**: the machine exposes an event hook (`Call`, `Exit`, `Redo`,
  `Fail`, `Cut`) with the current frame chain.  `:trace` in the REPL and a
  `--trace` flag on `infera run` are the first consumers; a `:why` that replays
  the last failing branch is the second.

### Module layout after step 1

```
src/Infera/Machine/Heap.hs      cells, trail, interning, Term <-> heap
src/Infera/Machine/Control.hs   frames, choice points, driver loop, cut, LCO
src/Infera/Machine/Builtins.hs  the current builtin table, ported
src/Infera/Machine/Table.hs     tabling on mutable tables
src/Infera/Engine.hs            thin: solveQuery / answers / runInfera over the machine
src/Infera/Engine/Reference.hs  today's engine, kept for differential testing until step 2 lands
```

### Milestones

1. Heap, trail, unification, `Term` round trip; property tests against
   `Infera.Unify` (same success/failure and same bindings).
2. Control: facts and rules, backtracking, cut, if-then-else, negation,
   `findall`, `once`; the whole existing suite passes against the new engine
   with CLP and tabling still routed through adapters.
3. LCO and the removal of `maxResolutionDepth`; `loop 1000000` runs.
4. CLP store over the heap with watched bits; the CLP examples and
   correctness models pass.
5. Tabling on mutable tables; dynamic facts; output log; determinism commits.
6. Tracing hook, `:trace`, runtime error positions.
7. Delete the reference engine once the differential suite has run clean for a
   release.

**Targets**: naive reverse at 2 million inferences per second or better
(about 10x), no depth bound, memory per activation bounded by the frame size.

### Risks

* Heap-resident terms make `Term`-based code (answer projection, tabling
  canonicalisation, sort checks) copy more; keep those at the boundaries.
* Getting cut barriers right inside `call`/`findall`/tabling is where Prolog
  engines go wrong; the existing cut tests plus the correctness models are the
  guard.
* `ST`-based code is less composable than the current pure functions; keep the
  machine small and keep inference, parsing and CLP propagation pure.

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

Declarations and inference feed the compiler: a predicate known `semidet`
with its switch argument bound compiles to `trust_me` after the first
matching clause; declared `det` inserts the failure check; inferred `<=`
positions allow `get_*` instructions to skip the trail check.

### Runtime

The machine from step 1 gains an instruction loop; frames become environments
with `Y` registers; builtins, CLP, tabling, output and dynamic facts are
unchanged because they already sit behind the machine interface.  Bytecode is
produced at load time and cached per predicate, so the REPL's incremental
clause additions recompile one predicate.

### Milestones

1. Compiler and VM for facts and first-order rules (no control constructs);
   differential test against the step 1 machine on the stdlib.
2. Control constructs and cut barriers; the full suite.
3. Indexing instructions; environment trimming; LCO in `execute`.
4. Determinism-directed code generation from declarations and inference.
5. Benchmarks in CI with regression thresholds.

**Targets**: 8 million inferences per second or better on naive reverse (within
2x of Scryer), with the step 1 debugger and tracer still working through the
instruction loop's event hook.

## Explicitly not planned

* A JIT: Prolog JITs have a poor record, GHC is an awkward host, and the
  workloads this language targets are search and constraint bound, where
  indexing, tabling and propagation strength dominate instruction dispatch.
* Changing the surface language: every example and test in the repository is
  the acceptance suite for both steps.

## Validation throughout

* The 73 Hedgehog tests (including the correctness models and the signature
  golden file) must pass against each engine.
* The examples' printed output is compared byte for byte between engines
  (the same check used when the inference changed).
* `test/cli.py` exercises the binary end to end.
* A benchmark script (`bench/`) runs naive reverse, the counting loop, `fib`,
  8 queens with and without CLP, SEND+MORE=MONEY and the breadboard placer, and
  CI fails on a regression of more than 20% against the recorded baseline.
