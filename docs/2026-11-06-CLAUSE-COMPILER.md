# Compiling whole clauses to native code - 2026-11-06

Kind: design proposal. Follows item 5 of
[`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md) ("make
the JIT a compiler rather than a shape matcher") and the "Large" items of the
2026-11-05 evening review. Base is `main` at `9cf276b`.

## Why

After the list kernels, every benchmark but one is within about 1.3x of
SWI-Prolog
([`2026-11-05-BENCHMARKS-EVENING.md`](2026-11-05-BENCHMARKS-EVENING.md)). The
exception is deriv, at 4.2x, and the native tier does nothing for it. The
tier today is a set of shape matchers: self-recursive tail loops over
integers and lists (at most four arguments, no structures, no other calls),
two list-search kernels, and two hand-matched callers (`safe/1`, `nrev/2`).
Anything else runs on the interpreter, whose per-call cost is about 170 ns
against SWI's 30-45 ns
([`2026-11-05-PER-CALL-WORK.md`](2026-11-05-PER-CALL-WORK.md)).

What the benchmark predicates need, from `INFERA_JIT_DEBUG=1` and `:sig` at
`9cf276b`:

| predicate | inferred | today | what native code would need |
| --- | --- | --- | --- |
| `d/3` (deriv) | semidet only when args 1 and 3 are ground; called with 3 unbound, so nondet | outside fragment | structures in both modes, non-tail calls, `ground`/`is_int`/`not (C == X)`, choice points that outlive the call |
| `expr1..4/1` | semidet | outside fragment | building nested structures |
| `fib/2` | semidet (arg 1 ground) | outside fragment | non-tail calls, arithmetic |
| `len/2` | semidet (arg 1 ground) | outside fragment | a non-tail call, arithmetic after it |
| `sieve/2` | semidet (arg 1 ground) | outside fragment | a call to another compiled predicate (`remove/3`), output list |
| `range/3` | nondet | declined | choice points (head repetition vs `<`) |
| `perm/2`, `sel/3` | nondet | declined | choice points that outlive the call, building |
| `next_to/3`, `zebra/1` | nondet | declined | choice points, calls into the list kernels |

Two observations decide the design:

1. **Native call frames alone are not enough for deriv.** `d/3` commits
   after its first answer only when its output argument is ground, and
   deriv calls it with the output unbound (`d A x _`). The catch-all clauses
   `d X X 1` and `d C X 0` overlap every structural clause, so each call
   leaves choice points behind, and the program goes on running while they
   are alive; only the enclosing `once` removes them. So native choice
   points must survive the native call's return, and the interpreter (and
   its collector) must run while they exist.
2. **Once native state survives a return, "bail out and rerun on the
   interpreter" stops working.** Today every kernel failure mode that is not
   plain success or failure (a full heap, a full trail, an arithmetic error,
   an unexpected tag) unwinds to the entry marks and reruns the call
   interpreted. That is sound only while a native call is one indivisible
   span. After a native call has returned one answer and is resumed by
   backtracking, there is no entry to rerun from. Native code then needs to
   pause (exit to the driver with its state intact), let the driver collect,
   grow the trail or raise an error, and resume.

## The model

A conventional WAM, in native code, side by side with the interpreter.

- **Native local stack.** One pinned, growable region per machine holding
  environment frames (permanent variables, the continuation's code address
  and frame) and choice frames (saved arguments, heap and trail marks, the
  alternative's code address, the cut barrier, the depth). The top of the
  stack is the higher of the newest environment and the newest choice, as in
  the WAM, so a frame a choice point can return to is never overwritten.
  Native code never uses the C stack for Prolog calls: calls store a return
  address in the frame and return through an indirect branch, so recursion
  depth is limited only by this region (the C stack of an `unsafe` foreign
  call is an OS thread stack and would overflow on deep recursion).
- **Word discipline.** Every slot in the native stack is either a tagged
  store word (what the collector already understands) or an untagged
  integer in a position the frame layout names (a code address, a frame
  link, a mark). Each frame starts with a header giving its kind and size,
  so the collector can walk the region without knowing which code pushed
  it.
- **One choice order.** Native choice points are not copied into the
  interpreter's `Choices`. Instead, when a native call returns success with
  native choice points still alive, the driver pushes one interpreter choice
  `AltNative` recording where those choices end in the native stack.
  Backtracking into `AltNative` resumes native code at the newest native
  choice; when the native choices for that entry are used up, `AltNative`
  is popped. Every interpreter choice also records the native stack top
  (`markStride` 5 to 6), so backtracking or cutting to it restores the top,
  which is what keeps native frames protected while an interpreter choice
  might return to them. Because nothing runs natively while an interpreter
  choice above the native ones is live, the two stacks stay in one
  consistent age order.
- **The binding boundary.** On a native return with live native choices
  the driver sets `rHB` to the newest native choice's heap mark, so the
  interpreter trails bindings of older cells just as it would for its own
  choices. Native code reads `rHB` at entry and keeps it current as it
  pushes and pops choices.
- **Pause and resume.** A native exit code `jitPause` with a reason (heap
  limit, trail capacity, error pending, call-out) leaves the native stack
  and a resume address intact. The driver handles the reason and re-enters
  at the resume address. A pause is also how native code calls a predicate
  it has not compiled: the driver runs the callee on the interpreter under a
  new continuation `CNative resumeAddr frame`, and `run'` re-enters native
  code when the continuation is reached, on each answer. The collector runs
  only in the driver, so it never runs during native execution, but now it
  can run while native frames are alive.
- **Collection with live native frames.** The collector gains one root
  set: the native stack's words, and the heap and trail marks in its choice
  frames, which are relocated exactly like `csMarks`. Native frames hold
  no pointers to GHC values, so nothing else changes.
- **Depth.** Depth stays continuation depth, as in `contDepth`: an
  environment frame records the depth of its call, a non-tail call compares
  it with `maxResolutionDepth`, and a last call does not deepen it. A
  resumed choice restores the depth it saved. `BranchExhausted` is reported
  at the same call with the tier on and off (the existing `jit_depth.py`
  gate, extended to nested calls).
- **Errors.** Native code does not raise. An error pauses with an error
  descriptor (kind, predicate, argument), and the driver raises the
  `SolveError` the interpreter would. Arithmetic and type errors must be
  raised at the same point in the same order as the interpreter, which the
  clause compiler guarantees by compiling goals in source order with the
  interpreter's evaluation order.

## The compiler

Source clauses, as today, but through a WAM-shaped intermediate code
instead of matching whole-predicate shapes:

1. **Clause code.** Each clause becomes `get`/`unify` instructions for its
   head (read and write mode, with the ground memo and the occurs check
   elided where a variable is a first occurrence, as `SRefOccurs` does in
   the stream), `put` instructions and `call`/`execute` for its body,
   `allocate`/`deallocate` for clauses with more than one call, and inline
   instructions for the builtins that matter (`is` and comparisons over
   immediates, `==`/`!=`, `ground`, `is_int`/`atom`/`var`/`nonvar`, `not`
   of an inline test, `=`). Anything else is a call-out.
2. **Selection.** Per predicate, a switch on the first argument's tag and
   functor that jumps to one clause or to a `try`/`retry`/`trust` chain over
   the clauses that remain, using the existing exclusivity analysis
   (`commitSafety`, `Infer.exclusive`) to drop a choice point where the
   clauses cannot both match. This is the native form of `candidateClauses`
   and replaces it for compiled predicates.
3. **Lowering.** The clause code lowers to the existing `JitOp` IR, which
   gains frame-relative loads and stores, a native call and return through
   the frame, a code-address constant, and the pause exit. Both assemblers
   implement them.
4. **Linking.** A program compiles as one unit per strongly connected
   component, so calls inside a component are direct branches and calls to
   another component go through a table the loader fills in. A predicate
   that cannot be compiled is a call-out target.

The existing kernels stay until the general path matches or beats each one
on its benchmark; then they are deleted.

## Increments

Each increment is its own branch, PR and dated report, with the gates below.

1. **Det islands.** The native stack with environment frames only, clause
   code, head and body structures in both modes, calls between compiled
   predicates, selection with `try`/`retry`/`trust` inside the call, and the
   inline builtins. A native call here must finish with no native choice
   point left: admitted only where the predicate commits on entry (det,
   or semidet with its switch arguments ground, checked at entry as the
   interpreter checks it), so any choice points it pushes are cut when it
   returns. The bailout-and-rerun exit still applies, because nothing
   survives the call.
   Expected to cover `fib`, `len`, `sieve` and `expr1..4`. Gate: fib and
   primes faster; nothing slower.
2. **Live native choice points.** Choice frames that outlive the call,
   `AltNative`, the native top in every interpreter choice, `rHB` on return,
   pause and resume for the heap limit, trail growth and errors, and the
   collector root set. Expected to cover `d/3`, `range/3`, `perm/2`,
   `sel/3`, `next_to/3`. Gate: deriv within 1.5x of SWI-Prolog; queens and
   zebra faster.
3. **Call-outs.** `CNative`, so a compiled clause may call any predicate or
   builtin, and admission becomes "everything but what is explicitly
   unsupported" (tabling, dynamic facts, constraints, findall and the
   control constructs, at first). Expected to cover the benchmark drivers
   and most ordinary programs. Gate: the in-engine table shows no case
   slower and the example programs agree in all modes.
4. **Retire the shape kernels** (`matchSafeLoop`, `matchNrevLoop`,
   `compileGeneralTailJit`, the scan kernel) once the general path matches
   them, and remove the ad hoc admission rules they need.

## Gates for every increment

- Full `cabal test all`, and every CI script (`cli`, `jit_depth`,
  `assert_scaling`, `autotable`, `det_guards`, `ite_parity`,
  `index_semantics`, `unify_scaling`, `example_programs --all-modes`, the
  bench harness tests).
- `core-engine parity` over `test/core/*.nprolog` with the JIT on and off,
  with `INFERA_CORE_STREAM=0`, and with `--gc-limit 1`. From increment 2 on,
  `--gc-limit 1` collects with live native frames at every call, which is
  the test the collector root set needs.
- A new parity corpus per increment (`test/core/parity-clause-*.nprolog`)
  covering each instruction, each pause reason, cuts across native and
  interpreter choices, and deep recursion.
- `INFERA_JIT_XCHECK` cross-check dumps, extended to calls that pause.
- x86-64 is verified only by Linux CI; every new IR op gets an encoding
  test in `test/JitEncodingTest.hs` and an `llvm-mc` disassembly check.
- Instructions retired (minimum of three) and `core-major` allocation on
  all benchmark cases, comparing builds with the same flags in fresh build
  directories.

## Risks

- **Collector interaction is where silent bugs will be.** A word in the
  native stack the root walk misses is a dangling reference after
  compaction, and the symptom appears later and elsewhere. Frame headers,
  an invariant checker that walks the native stack after every collection
  in test builds, and `--gc-limit 1` are the mitigations.
- **Cut across the boundary.** A cut in interpreted code must remove native
  choices above its barrier, and a cut in native code must remove
  interpreter choices above its barrier. Both go through the native top
  saved in each choice and through `AltNative`; both need dedicated tests.
- **Constraints.** Native code still declines when `rCLP /= 0`, because
  binding under constraints records into the bound log and wakes
  propagators. With live native choices that rule has to hold at every
  resume, not only at entry; a constraint store created while native
  choices are live must pause native code out or forbid its resumption.
- **Two engines.** Each increment adds native forms of things the
  interpreter does (selection, choice points, cut). The interpreter stays
  the specification, `INFERA_JIT=0` stays the escape hatch, and the parity
  corpus runs in both modes.
- **Size.** This is weeks of work. Increment 1 alone is the largest change
  the JIT has had, and increment 2 touches the driver, the choice stack and
  the collector. Each increment is useful on its own, so the work can stop
  after any of them.

## Not in scope

- Tabling, dynamic facts, CLP, findall and the control constructs
  (`or`, if-then-else, `not` of a general goal, `once`) stay on the
  interpreter and are reached by call-out.
- Generational collection, which would cut collection cost on deriv and
  primes (7-12%), is independent and can follow.
