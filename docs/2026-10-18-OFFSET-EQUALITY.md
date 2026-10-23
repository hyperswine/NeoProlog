# Domain-consistent offset equalities

Date: 2026-10-18

Linear equalities between two variables with unit coefficients, such as
`U #= Q + I`, `D #= Q - I` and `X #= 7 - Y`, are now domain-consistent in both
solver paths. Each domain is intersected with the image of the other, so a
value removed from the middle of one domain is removed from the other. Larger
linear sums keep bounds propagation.

## Problem

Writing `examples/queens.nprolog`, the natural model names the diagonals with
auxiliary variables and posts `all_different` three times:

```prolog
diagonals [] _ [] [].
diagonals [Q | Qs] I [U | Us] [D | Ds] <-
  U #= Q + I, D #= Q - I, I1 is I + 1, diagonals Qs I1 Us Ds.
# all_different Qs, all_different Ups, all_different Downs, label Qs
```

When labeling fixed a queen, `all_different` removed a value from the middle
of another `U`'s domain, but `U #= Q + I` propagated only bounds, so the
attacked square stayed in `Q`'s domain and was rejected by search instead of
propagation. The pairwise encoding `Q #!= Q1 + D, Q #!= Q1 - D` punches the
holes directly and was two orders of magnitude faster, which the example's
comment recorded as a workaround.

## Change

[`CLP.reduce`](../src/Infera/CLP.hs) and the mutable kernel's native
reducer in [`CLP.Mutable`](../src/Infera/CLP/Mutable.hs) recognise a
reduced linear equality whose coefficient map holds exactly two variables
with coefficients in {-1, 1} (`unitPair`). After substitution of bound and
aliased variables, `cx*x + cy*y + k = 0` is the bijection `x = a + s*y` with
`s = -cx*cy` and `a = -cx*k`. `propagateUnitPair` intersects `x`'s domain
with the image of `y`'s domain under that map (`shiftDomain`), then `y`'s
domain with the image of the new `x` domain under the inverse. The image of
an interval with holes is an interval with shifted or reflected holes, so the
work is linear in the number of holes. The result is a subset of what bounds
propagation produced, and the constraint stays in the store as before, so
answers still show the same residual (`Y - X #= 2`).

The two reducers compute the same pure function of the two domains, and the
Reference engine, the legacy machine and Core all use one of them, so the
ordered parity checks stay exact. The frozen differential oracle in
`test/ReferenceCLP.hs` compares only acceptance of complete assignments and
is unaffected. Equalities with one variable, with more than two variables, or
with non-unit coefficients take the previous bounds path.

## Measurements

The auxiliary-variable model above (`queens_aux`) and the pairwise model
(`queens_pair`) were timed with `core-engine time --core` on this Mac
(aarch64, GHC 9.8.2), one solution each, median of two runs after a warm run.
The N = 60 baseline shared the machine with a build and the test suite and
was stopped unfinished after 17 minutes.

| Model | N | Before | After |
| --- | --- | --- | --- |
| auxiliary diagonals | 24 | 2.2 s | 0.10 s |
| auxiliary diagonals | 30 | 10.5 s | 0.21 s |
| auxiliary diagonals | 60 | > 17 min, stopped | 1.6 s |
| pairwise disequalities | 30 | 0.04 s | 0.04 s |
| pairwise disequalities | 60 | 0.5 s | 0.5 s |

After the change both encodings visit the same boards: the first solution
found by `queens_aux` is the one `queens_pair` finds, at every size measured.
The auxiliary model remains about three times slower than the pairwise one at
N = 60 because it posts and wakes more constraints, so the shipped example
keeps the pairwise encoding and its comment now says why.

## Checks

* `test/core/parity-clp.nprolog` and `parity-mutable-clp.nprolog` gain
  queries where a hole crosses an offset equality in each direction, through a
  chain of two equalities, from `all_different` on auxiliary variables, and
  across a `pause` with rollback. Core, Reference and the machine agree on
  the ordered answers including the rendered domains.
* `offset_equality_domains` in `test/CLPPerformanceTest.hs` (group `clp`)
  generates random intervals, offsets, reflections, posting orders and holes
  on either side, and checks the persistent store's domains, Core's labeled
  answers and Core's rendered residual domains against a brute-force model.
* Answer order changes only where the README already allows stronger pruning
  to change the order of labeled solutions. No checked-in parity query or
  example output changed; the shipped `queens_clp` first answers are
  unchanged because that encoding posts no two-variable equalities.

`cabal test`, `infera-test --group core-engine` and
`python3 test/cli.py "$(cabal list-bin infera)"` pass.
