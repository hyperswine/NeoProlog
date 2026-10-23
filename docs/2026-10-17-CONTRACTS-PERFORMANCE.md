# Sorts, modes and determinism as performance - 2026-10-17

Infera's declarations and inference exist for correctness: a declared
signature is enforced at runtime, inferred signatures are advisory, and
inferred determinism drops choice points. This note records the intent that
they should also make programs *cheaper* to run than the same programs on an
engine without them, what that means mechanically, what is sound, and the
order in which the core implements it.

## Where things stood

Measured on the core as the public engine (commit 30892fe), process time:

| Program | Undeclared | Fully declared |
| --- | ---: | ---: |
| `len` and `app` over a 20,000-element list | 0.22 s | 30.97 s |
| guard-only `classify` in a 1M-iteration loop | 0.88 s | same (inferred semidet commits) |
| `fib 30` with inferred tabling | 0.01 s | n/a (SWI untabled 0.67 s, Scryer 0.40 s) |

Declaring `len : det (list int: <=) (int: =>)` made the program 140x
slower: the call-entry sort check walks the whole list on every recursive
call, and a declared output list is walked again at every return. The
determinism contract removed choice points but saved nothing measurable
against SWI, which tolerates those choice points. The only existing win is
inferred tabling, an asymptotic change that needs no declaration.

So the first obligation is that declarations must never cost more than a
constant at the boundary where they cannot be proven. Only then can they be
used to go faster.

## The intent

1. **Checks are paid once, at boundaries.** A declared contract is verified
   where the engine cannot prove it (a query, a call from an undeclared
   predicate, a call whose arguments have unknown shape). Inside declared
   code, a call whose arguments provably satisfy the callee's contract skips
   the entry check, and a clause whose result provably satisfies its own
   contract skips the return check. This is how Mercury treats its
   declarations, and it is what makes them free.
2. **Determinism buys control-stack reuse, not only pruning.** A declared
   `det`/`semidet` call that needs no return check and no success guard can
   continue with its caller's return frame, so deterministic recursion over
   declared predicates runs with a bounded continuation, as undeclared
   tail recursion already does.
3. **Ground inputs buy cheaper matching.** A head argument that is known
   ground cannot contain the variable being bound, so matching it needs no
   occurs check, and the ground memo can be set without a walk. A known
   `int` input needs no tag test before arithmetic.
4. **Determinism buys choice-point-free clause selection.** When the
   inference proves a predicate semidet because its clause guards are
   exclusive, the guards can commit as soon as they pass instead of leaving
   a choice point for the body's duration (Mercury's switch detection as an
   early commit).
5. **Inference stays advisory for soundness, mandatory for cost.** Only
   declared contracts, verified at entry or proven from verified facts, may
   remove a check or a trail entry. Inferred signatures may only decide
   things that cannot change answers: which choice points to drop, what to
   table, which index to prefer.

## Soundness of check elision

Facts are per activation and only ever strengthen along a success path,
because bindings persist until backtracking discards the activation.

* **Head facts** come from the enclosing predicate's declared signatures.
  With several alternatives the runtime selects the first whose input
  arguments are ground; the proof uses only what holds under every
  alternative: an argument is ground if it is `<=` in all of them, and its
  sort is the join of their sorts. Facts flow into head patterns: an
  argument of sort `list S` matched against `[H | T]` gives `H : S` and
  `T : list S`, both ground.
* **Body facts**: `X is E` gives `X` ground and `int` when every operand is
  `int`, otherwise `num`; `X = c` gives the constant's sort; a call to a
  predicate with declared signatures gives its `=>` arguments their declared
  sort, ground, because the callee verifies or proves that contract itself.
  `<=>` arguments give no fact: a non-ground term of sort `list int` can
  stop being one when a later binding fills a hole, so only ground facts are
  kept. Control constructs contribute no facts outward.
* **Call elision**: a call to `Q` with declared signatures selects the first
  alternative whose `<=` arguments are all provably ground; the runtime
  then takes that alternative without testing groundness, and skips the
  sort test of every argument whose proven sort is a subsort of the declared
  one or which is a fresh variable (a variable satisfies every sort).
  Untrusted arguments are still checked.
* **Return elision**: a clause's return check is skipped when, under the
  facts at the end of its body, every argument pattern of its head has a
  proven sort within the declared sort of every alternative, and every `=>`
  argument is proven ground. When all clauses of a predicate qualify, the
  call pushes no return-check frame at all, which is what lets the call
  continue with its caller's frame.
* The induction closes because every elided check is justified by a check
  that did run (at the boundary) or by a proof of the same kind one level
  down; no inferred signature participates.

## Step 1 results (same day)

The compiler now carries a fact environment through each clause (slot is
ground with sort S), seeded from the enclosing predicate's declared inputs
and extended by `is`, constant unification, type checks and the declared
outputs of calls. Each call to a declared predicate carries a `Trust`: the
alternative to select without testing groundness and the arguments whose
sort check is proven. Each clause records whether its return check is
proven; when every clause of a predicate qualifies, calls push no return
check, and a call needing only a commit or a determinism guard shares its
caller's committing return frame. Determinism guards moved from boxed choice
points to an unboxed stack (height, success flag, key): a committing return
marks and removes every guard pushed since its base, a cut removes guards
above its height, and backtracking fires the guards it passes.

| Program (process time, peak RSS) | Before | After |
| --- | ---: | ---: |
| declared `len`/`app`, 20,000 elements | 30.97 s | 0.09 s (undeclared 0.07 s) |
| `count` to 1,000,000, declared `det` | 1.82 s, 563 MB | 0.32 s, 137 MB |
| `count` to 1,000,000, declared `semidet` | 0.28 s, 81 MB | 0.28 s, 81 MB |
| `count` to 1,000,000, undeclared | 0.20 s, 81 MB | 0.20 s, 81 MB |

A new parity file, `test/core/parity-contracts.nprolog`, keeps the boundary
behaviour: sort and mode errors at query calls, output-sort errors inside
declared predicates, determinism errors, multiple alternatives, aliasing
and widening/narrowing declarations all still produce the reference's
answers and errors. The one deliberate difference is depth: the reference
and the old machine exhaust their resolution limit on a 100,000-deep
declared `det` recursion and report a determinism error, while the core
runs it in constant control space; the parity query stays within the
reference's limit.

What remains: `det` still costs one guard record per call (24 bytes) for
the failure obligation, since a call that could fail must be able to report
it; `semidet` carries no such obligation and is the declaration to use for
deterministic loops. Undeclared code is unaffected: the CLI harness after
this step records reverse 0.42 s, loop 0.031 s, fib 0.068 s and queens
0.031 s, the same as before it. Steps 2-4 below are not started; of them,
only the guard commit (3) is expected to be measurable, and only on
predicates whose clauses are selected by guards rather than by indexing.

## Order of work

1. Static contract proofs in the compiler and their use at call and return
   (this document's first implementation). Target: the declared `len`/`app`
   program within 10% of the undeclared one, and declared deterministic
   list builders running with a bounded continuation.
2. Ground-input matching: skip the occurs check and set the ground memo
   directly when a head argument is proven ground.
3. Guard commits for inferred exclusive guards.
4. Unboxed `int` operands where the sort is proven.

Each step is gated by the `core-engine` parity group and the example sweep;
a declaration may change speed, never answers.
