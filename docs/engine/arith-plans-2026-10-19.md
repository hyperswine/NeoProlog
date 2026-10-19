# Compiled arithmetic plans - 2026-10-19

Branch `core-unboxed-control`, base `e47bc65`. Follows the
[clause selection report](clause-selection-2026-10-19.md). The
[control stacks report](control-stacks-2026-10-19.md) profile put
`evalFast` at about 14% of Core time on Fibonacci. `evalFast` walks an
`Expr` tree recursively and passes every intermediate value through the
`rVAL` store register. Most arithmetic in practice has one of a few flat
shapes: `N > 0`, `N1 is N - 1`, `F is F1 + F2`.

## What changed

**Plans.** [Compile.hs](../../src/Infera/Core/Compile.hs) adds a `Plan`
type, derived from an `Expr` by `exprPlan`:

| Plan | Shape | Example |
| --- | --- | --- |
| `PlanImm k` | immediate integer | `0` in `N > 0` |
| `PlanSlot v` | slot | `N` in `N > 0`, `Y is X` |
| `PlanSI op v k` | slot op immediate | `N - 1` |
| `PlanIS op k v` | immediate op slot | `1 - X`, `100 / X` |
| `PlanSS op v w` | slot op slot | `F1 + F2` |
| `PlanNone` | anything else | `A * B + C`, `neg X`, `X ^ 2`, `1.5 * X` |

The binary plans cover the operators that `evalFast` handles: `+`, `-`,
`*`, `/`, `%`, `min`, `max`. `GIs` now carries the plan of its expression,
and `GCmp` carries the plan of each side. Nothing else about the goals
changed.

**Running a plan.** [Run.hs](../../src/Infera/Core/Run.hs) `runPlan`
dereferences the slot words and reads them as immediate integers. It
returns the result as an `Int`, or `planMiss` (`minBound`; no immediate
integer has that value). `planApply` reproduces the bounds of `evalFast`
exactly:

* `+`, `-`: the result must lie in `[-2^60, 2^60)`;
* `*`: both factors must be below `2^30` in magnitude;
* `/`: the divisor must be non-zero and the quotient must fit;
* `%`: the divisor must be non-zero;
* `min`, `max`: always succeed.

A plan misses when an operand is not an immediate integer (unbound, a
bignum, a float, an atom, a string or arithmetic data) or when a bound
fails. On a miss, `GIs` and `GCmp` go straight to the general evaluator
(`evalExpr`, or `compareGoal` for comparisons). That evaluator owns
errors, bignums, floats and instantiation errors, as before. A plan covers
exactly the shapes where `evalFast` would compute the same value under the
same bounds, so after a miss the old `evalFast` would also have failed.
Because of that, a miss skips it. `PlanNone` expressions keep the previous
route: `evalFast`, then the general evaluator.

For a comparison, the plan route is taken only when both sides have plans.
The right side runs only if the left side produced a value, as in
`evalFast`. A hit binds the target through `numericTarget` and `unify`,
the same as the old fast path.

**Relocated plans.** Collection can detach suspended goal plans from their
activation, and turns slots into words when it does
([Liveness.hs](../../src/Infera/Core/Liveness.hs)). It rebuilds each plan
from the relocated expression with `exprPlan`. Relocated slots are no
longer slots, so those goals get `PlanNone` and take the old route.

**One store read per goal.** The first version raised GHC allocation by
13-17% on Fibonacci and loop. The STG showed one `mStore m` selector thunk
per use in the new local `bindQuick` and `general` helpers. Both
alternatives now bind the store once with a strict `where` binding.
Allocation is now identical to the base on every measured workload.

## Semantics kept

* Evaluation order: left operand, then right; the left side of a
  comparison, then the right side.
* Errors: no plan raises an error. Division or modulo by zero, float
  operands to `%`, non-numeric operands and unbound operands all miss and
  reach `evalExpr` or `compareGoal`, which raise the same errors as
  before.
* Results that leave the immediate range miss and are computed as bignums
  by the general evaluator.
* `numericTarget` is unchanged: a numeric result binds a slot target
  through its local reference.
* The leading integer guard used by clause selection still reads `GCmp`
  operands from its expressions, and is unaffected.

## Measurements

`bench/core-major`, `-O2`, macOS arm64. Base is a binary built from
`e47bc65`. Runs alternate base and new processes, one sample per fresh
process. Each cell is a per-query median.

The machine was heavily loaded by unrelated builds during every run (load
average 10-17), so absolute times are 10-35% above the previous report.
Reverse (`core-nrev`) runs no arithmetic and serves as the control.

Batch 20, 21 processes per binary:

| Workload | Base CPU ms | New CPU ms | Change | Base alloc MiB | New alloc MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fibonacci 25 | 56.75 | 50.00 | -12% | 64.7 | 64.7 |
| Loop, 90,000 | 13.26 | 12.13 | -9% | 12.4 | 12.4 |
| First 8-queens | 12.79 | 12.02 | -6% | 19.4 | 19.4 |
| Reverse (control) | 10.63 | 10.58 | -0% | 18.5 | 18.5 |

Batch 20, an earlier set of 9 processes per binary:

| Workload | Base CPU ms | New CPU ms | Change |
| --- | ---: | ---: | ---: |
| Fibonacci | 57.25 | 51.77 | -10% |
| Loop | 11.93 | 11.32 | -5% |
| Queens | 10.28 | 9.69 | -6% |
| Reverse (control) | 9.80 | 9.10 | -7% |

Batch 1 (a single query of about 10 ms per process) was too noisy under
this load to separate changes below 10%. The control moved between -7%
and +11% across sets. Fibonacci measured -6% and -10%, loop -3% and -8%.
Queens measured +3% and +7%.

Fibonacci gains 10-12% from four arithmetic goals per call. Loop gains
5-9% from two. Queens gains about 6% in batch 20. Its arithmetic is
the three `is` goals in `noatt` (`Q1 - Q`, `Q - Q1`, `D + 1`), which take a
smaller share of its time beside permutation search and disequalities. These gains should be confirmed on a quiet machine. Allocation is
unchanged: `evalFast` was already allocation-free, and the gain comes from
no tree walk and no `rVAL` round trips.

## Validation

* Full Haskell suite: 497 checks. The new parity file adds one check
  through `CoreTest`'s parity list.
* [test/core/parity-arith.nprolog](../../test/core/parity-arith.nprolog),
  65 queries: every planned shape at the immediate boundary in both
  directions (`2^60 - 1 + 1`, `-2^60 - 1`, `1 - (-2^60)`, doubling `2^59`,
  products at `2^30`); bignum operands to planned goals;
  `-2^60 / -1`; division and modulo by zero with immediate and slot
  divisors; float operands, including float zero divisors and `%` on
  floats; atoms, strings and unbound variables in planned comparisons and
  `is`; bound and float targets of `is`.
* `core-engine parity` over every example and parity file except blocks
  and database_access (31 files, 577 queries): all agree with the
  reference and the legacy machine, both normally and with `--gc-limit 1`.
* `python3 test/cli.py`: all acceptance groups pass.
