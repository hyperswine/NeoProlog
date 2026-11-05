# Native list filters: `remove/3` - 2026-11-05

Kind: engine change and measurement. Follows
[`2026-11-05-SCAN-KERNEL.md`](2026-11-05-SCAN-KERNEL.md); base is
`perf/mem-kernel` at `14c7cd9`. Item 2 of
[`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md) made
determinism inference prove `remove/3` semidet; this change lets the JIT
use that.

## Why `remove/3`

primes spends almost all of its time in the sieve's filter:

```
remove _ [] [].
remove P [I | Is] Nis <- 0 is I % P, remove P Is Nis.
remove P [I | Is] [I | Nis] <- X is I % P, X != 0, remove P Is Nis.
```

It is the shape the general tail compiler already handles for `app/3`:
list in, list out built by tail recursion modulo cons, with integer
guards. Since the guard-prefix inference it was inferred semidet when its
first two arguments are ground, so the JIT stopped declining it as
nondeterministic, but it was still "outside JIT fragment" for three
reasons, each fixed here.

## Changes

1. **`%` in native code.** New IR instruction `JModChecked dst a b bail`,
   floored like Haskell's `mod` (the result takes the divisor's sign), with
   a zero divisor going to `bail` so the interpreter raises the error.
   AArch64: `sdiv`, `msub`, then add the divisor back when the remainder is
   non-zero and its sign differs. x86-64: `cqo`, `idiv`, the same
   correction on `rdx`. Operands are unboxed 61-bit integers, so `idiv`
   cannot overflow and the result always fits. `compileArithExpr` accepts
   `mod` next to `plus`, `minus` and `mul`.
2. **`k is E` as a guard.** With a literal on the left, `is` evaluates `E`
   and compares the result with `k` by identity; both are integers on the
   compiled path, so it is an equality test. `isGuardOrIs` admits it and
   `compileOneGoal` compiles it as a compare and branch.
3. **Exclusivity through expressions.** Native code commits to the first
   clause whose head and guards hold, so each recursive clause must exclude
   every later one. `Jit.clausesExclusive` only ranged head paths, so it
   could not see that `0 is I % P` and `X is I % P, X != 0` never both
   hold. The new `exprConstraints` keys an arithmetic expression by its
   form with head variables replaced by their argument paths (the same key
   in two clauses of one predicate is the same value for the same call),
   and ranges it from `k is E`, from comparisons of `E` with a literal, and
   from comparisons or `!=` on a variable defined by `X is E`. `!=` counts
   only on such a variable: on an unevaluated expression it is structural
   (`I % P != 0` always holds), which the corpus checks. The range update
   is now one shared `refineRange`.

The determinism inference and this JIT check are still two analyses; the
JIT one now covers what `remove/3` needs, not everything inference proves.

## Results

Instructions retired, millions (`/usr/bin/time -l`, minimum of three),
`14c7cd9` against this change, both built with `--enable-optimization=2`
in fresh build directories:

| case | before | after | change |
| --- | ---: | ---: | ---: |
| primes 20000 | 14606 | 1384 | -90.5% |
| zebra x300 | 4233 | 4229 | 0% |
| deriv x30000 | 9809 | 9813 | 0% |
| queens 9, all | 9346 | 9350 | 0% |
| nrev 30 x 30000 | 5081 | 5079 | 0% |

`bench/run.py --case primes --runs 5 --warmup 1`, whole process, medians,
load average 6-12 on this M4 (SWI-Prolog 10.0.2, Scryer 0.10.0):

| case | before | after | SWI-Prolog | Scryer |
| --- | ---: | ---: | ---: | ---: |
| primes | 0.658 s | 0.078 s | 0.358 s | 0.732 s |

primes goes from about 1.8x slower than SWI-Prolog to 4.6x faster. The
filter's elements cost a few native instructions each, where SWI-Prolog
runs `remove/3` through its virtual machine.

The kernel falls back to the interpreter 37 times in primes 20000, each
when the output list would cross the collection limit; the existing
allocation backoff keeps that from repeating. `sieve/2` (it calls
`remove/3`), `len/2` (not a tail call) and `range/3` (left nondeterministic
on purpose: `range N N [N]` against `I < N`) stay interpreted.

A note on baselines: an earlier comparison against a binary built with
different flags showed queens 4% slower. Rebuilt like for like, the
difference is gone, and the STG of `Infera.Core.Run` and of
`invokeJitKernel` is identical in the two builds.

## Correctness

- `test/core/parity-filter.nprolog` (new, in the `core-engine` group, 30
  queries): the filter at every residue, negative elements and divisors
  (floored results), a zero divisor (same error), atoms, floats, big
  integers, unbound elements, divisors and tails (all to the interpreter),
  bound and partly bound outputs, `1 is I % 2` with `X < 1`, `%` in a
  counting loop, two filters that are not exclusive (different divisors;
  structural `!=`), and the primes sieve.
- `core-engine parity` over `test/core/*.nprolog` agrees normally and with
  `--gc-limit 1`, and on the new corpus with `INFERA_JIT=0` and
  `INFERA_CORE_STREAM=0`.
- Full `cabal test all`, and every CI script: `cli`, `jit_depth`,
  `assert_scaling`, `autotable`, `det_guards`, `ite_parity`,
  `index_semantics`, `unify_scaling`, `example_programs --all-modes`, the
  bench harness tests.
- Both encodings of `JModChecked` were assembled and disassembled with
  `llvm-mc` (register and spilled operands, every branch target checked).
  The x86-64 sequence runs only on Linux CI; this host is AArch64.

## Not done

- **One exclusivity analysis.** `Infer` and the JIT still reason
  separately; the JIT could take the clause pairs inference proved
  exclusive instead of re-deriving them.
- **`sieve/2` and `len/2`.** A call to another predicate inside a kernel
  and non-tail recursion both need item 5 of the unification-heavy plan
  (compile the clause stream, with a native frame stack). With `remove/3`
  native, they are now most of what primes has left.
