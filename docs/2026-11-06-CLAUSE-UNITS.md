# Clause units: det islands - 2026-11-06

Kind: engine change and measurement. Increment 1 of
[`2026-11-06-CLAUSE-COMPILER.md`](2026-11-06-CLAUSE-COMPILER.md); base is
`main` at `63ee3ce`.

## What landed

Whole predicates now compile to native code, not only the shapes the
kernel matchers know. A **clause unit** is an entry predicate and every
predicate it reaches (`Infera.Core.Jit.Clause`):

| Part | What native code does |
| --- | --- |
| Head | matches every argument in read and write mode: atoms, characters, integers, nested structures and lists, repeated variables (unification without a walk where both sides are known), occurs checks where a variable is not a first occurrence |
| Body | `is` over `+ - * %` (overflow and non-integers rerun on the interpreter), `> < >= <=`, `!=` on constants, `=` with a term, `true`, and calls to the unit's own predicates |
| Calls | environment frames on a native stack (not the C stack); a call stores its return address (`JLoadLabel`) in the callee's frame and the callee returns through it (`JJumpReg`); a last call reuses the frame |
| Selection | clauses tried in order; a clause that fails before it commits is undone from the trail; commit after the head and the leading guards |
| Depth | continuation depth as in the interpreter: non-tail calls tick, last calls do not |

A unit exits with success, failure, "declined" (a pre-flight ground
check failed), or "rerun": the call is unwound to its entry and run on the
interpreter, which covers a full heap or trail, arithmetic errors, an
unbound value where a head reads, and anything else native code cannot
finish. A full native stack (4096 words initially) grows fourfold and
reruns the call natively, up to 64 Mi words.

**Commit safety.** Native selection never leaves a choice point, so every
predicate in a unit must prove that, once a clause's head and guards hold,
no later clause could also match. The proofs are the existing exclusivity
analysis, moved to `Infera.Core.Jit.Exclusive` and extended to atoms,
characters and functors: heads that differ at a read-only input path,
guards that the integer analysis or determinism inference proves
exclusive, or inferred semidet with the switch arguments ground. Output
arguments are masked out of every proof.

**Admission.** A predicate roots a unit when it is det or semidet,
undeclared, not tabled or dynamic, has at most 8 arguments and 16 clauses,
and everything it reaches is in the fragment above. In the benchmark file
that is `fib`, `len`, `sieve` with `remove`, and `expr1..4`. `d/3` is
outside (`is_int`, and its choice points outlive the call: increment 2),
and so are the drivers (`once`: increment 3).

## Bugs the gates found

1. **A guard proof under aliasing.** `p X 1 <- X > 0. p X -1 <- X <= 0.`
   The guards are exclusive for any one value of `X`, but the query
   `p U U` binds `X` through the second argument to a different value in
   each clause, and both clauses answer. Native code committed after the
   first. The guard-based proofs now also require the arguments the guards
   read to be ground at entry, which a head binding cannot change. Two
   existing generated-property tests caught this
   (`infer alias guard is sound`, `aliased call arguments retain both
   guarded answers`), and `sgn` in the new corpus covers it.
2. **The stack-growth retry ran on the wrong arguments.** Native calls
   reuse the argument slots, so after a full stack the slots held some
   inner call's arguments, and the retry answered for those. The retry now
   reloads the call's arguments from the store. `jit_depth.py` and the
   parity suite caught it.
3. **`core-engine parity` cannot see a first-run-only bug.** It solves each
   query more than once and compares a later run, by which time the native
   stack had grown, so bug 2 passed the command-line parity check while
   the cabal parity suite (which compares the first run) failed. Worth
   knowing for increment 2, whose state also persists across calls.

The new corpus `test/core/parity-clause.nprolog` (92 queries) covers each
head and body form, errors and unbound inputs, structure building in both
modes, mutual recursion, commit-on-success selection, and 3000-frame
non-tail recursion that grows the native stack twice.

## Compile on first call

Compiling every admitted predicate at load cost about 20M instructions in
the benchmark file (7M planning, 7M assembly, 9M installing seven units),
about 13% of `loop`'s whole run, which uses none of them. Making the
`pJit` field lazy fixed that but cost zebra 1.4%: a few instructions on
every call to check the field. What landed keeps the field strict, runs
only the cheap fragment check at load, and gives each admitted predicate a
deferred kernel (`jkScan = -3`) whose unit is planned, assembled and
installed when it is first called. Predicates outside the fragment pay
nothing per call.

## Measurements

GHC 9.8.2, `aarch64-darwin`, `--enable-optimization=2`, `main` (`63ee3ce`)
and this branch in fresh build directories.

Instructions retired, millions, whole process (`/usr/bin/time -l`, minimum
of three, `bench/run.py` goals, every answer validated):

| case | `main` | clause units | change |
| --- | ---: | ---: | ---: |
| fib 25 | 986 | 206 | -79% |
| deriv x30000 | 9571 | 9173 | -4.2% |
| zebra x300 | 4075 | 4063 | -0.3% |
| nrev 30 x 3000 | 655 | 654 | 0% |
| queens 8 | 241 | 240 | 0% |
| primes 20000 | 1343 | 1345 | +0.1% |
| loop 90000 | 166 | 167 | +0.6% |

Allocation per query, `core-major --case C --batch 5` (exact):

| case | `main` | clause units |
| --- | ---: | ---: |
| core-fib | 82.30 MB | 8.57 MB |
| core-nrev | 9.678 MB | 9.677 MB |
| core-loop | 8.575 MB | 8.575 MB |
| core-queens | 12.98 MB | 12.93 MB |
| example-sudoku4, river, job-shop, routes, packing | | within 0.03% |

fib is the case this increment was for: two non-tail calls and arithmetic
around them, now one native unit. deriv
gains from `expr1..4` (built natively) and still spends its time in `d/3`.
primes was already native through the filter kernel. The `loop` and
`primes` differences are within run-to-run spread. The design's gate
("fib and primes faster; nothing slower") holds for fib, and primes is
unchanged because its filter was already native.

## Correctness

* `cabal test all`, including the new x86-64 encoding tests (`lea`
  rip-relative to the label for every register, `jmp r64`, the 64-byte
  spill area) and a native test that jumps through a loaded label address
  on this host. The byte sequences were checked against `llvm-mc`.
* `core-engine parity` over `test/core/*.nprolog` with the JIT on and
  off, with `INFERA_CORE_STREAM=0`, and with `--gc-limit 1`.
* Every CI script, `example_programs --all-modes`, and the bench harness
  tests.
* x86-64 runs natively only on Linux CI.

## Open

* Increment 2 (choice points that outlive the call) is what deriv needs.
* `count/2`-shaped predicates still go to the tail-loop kernel first; the
  shape kernels are retired in increment 4.
* `!=` on structures, `ground`, type checks and `not` of an inline test are
  not inline yet; a goal outside the fragment declines the whole unit
  until call-outs (increment 3).
