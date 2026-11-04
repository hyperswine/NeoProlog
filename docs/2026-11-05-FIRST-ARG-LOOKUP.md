# First-argument lookup on fact tables: it was load time - 2026-11-05

Kind: diagnosis and fix. Follows
[`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md) and the
2026-11-05 unification benchmarks, which had Infera about 20x behind
SWI-Prolog on a 2000-fact lookup program.

## The workload

`index`: 2000 facts `fact I aI cK`, then 200000 iterations of
`fact I At C, fact J At _, (C = c3 -> ... ; ...)`. Each call does one
first-argument lookup (I bound) and one second-argument lookup (J unbound,
At bound).

## Finding

Lookups were not the cost. Selection already uses a precomputed per-argument
table (`ArgIndex`: an `IntMap` from immediate key to shared candidates).
Profiling (`--profiling-detail=toplevel-functions`) showed:

- **Determinism inference was quadratic in the number of clauses.**
  `Infer.inferDets` called `exclusive` for every pair of clauses, twice per
  fixpoint round (once for the switch positions, once for the check).
  `exclusive` + `indexKey` + `distinctPatterns` + `inferDets` were about
  50% of the run and 60% of the allocation. Load time was 0.96 s for 2000
  facts and 3.5 s for 4000.
- **The module loader appended each item with `acc ++ [item]`.** This was
  52% of a 4000-fact load once the first problem was gone.

## Changes

1. `pairwiseExclusivity` runs once per predicate. For fact tables it takes a
   linear path (`atomicSwitch`), used when no clause has a cut or guard and
   some position up to which all head arguments are atomic has pairwise
   distinct keys. It returns exactly what the pairwise check returns: the
   same Bool and the same switch positions in the same order. A predicate
   that is not pairwise exclusive starts `Nondet`, where `step` would take
   it anyway. Checked: `:sig` output is identical on all 74
   example/test/bench programs and on 450 random fact tables.
2. `expandLocatedItems` accumulates in reverse.

## Results

linux-x86_64, GHC 9.8.2 `-O2`, noisy shared VM, wall clock for the whole
process, median of 5 (JIT on) or 3 (JIT off), `<- notable.` programs.
Before is main at d2c56c4.

| case | JIT | before | after | change |
| --- | --- | ---: | ---: | ---: |
| index (2000 facts) | on | 1.185 s | 0.249 s | 0.21x |
| index | off | 1.074 s | 0.243 s | 0.23x |
| load only, 2000 facts | on | 0.96 s | 0.06 s | |
| load only, 4000 facts | on | 3.5-3.9 s | 0.12 s | |
| bst 30k | on | 3.622 s | 3.260 s | 0.90x |
| zebra | on | 2.448 s | 2.476 s | 1.01x |
| primes | on | 1.280 s | 1.322 s | 1.03x |
| deriv (renamed functors) | on | 3.520 s | 3.704 s | 1.05x |
| nrev | on | 0.428 s | 0.423 s | 0.99x |
| tak | on | 0.718 s | 0.692 s | 0.96x |
| queens 9 | on | 0.706 s | 0.714 s | 1.01x |
| findall 50k | on | 0.639 s | 0.601 s | 0.94x |

SWI-Prolog 10.0.0 runs `index` in 0.057 s, so Infera is now about 4x
behind it on that program, down from 20x. The other cases do not involve
large predicates and stay within run-to-run noise (about ±5% on this VM).
All answers are identical.

## Tests

`test/index_semantics.py` (in CI):
- the answers of a mixed predicate match SWI-Prolog's, in order and count:
  bound and unbound first argument, variable heads between keyed ones,
  compound and list keys, a body-guarded clause, cut, and if-then-else;
- the index follows assert and retract of dynamic facts;
- loading 4x the facts takes less than 10x the time;
- every query runs with the JIT on and off.

## Not changed, noted

- The occurs-check decision was not moved to load time. The ground-mark
  memo in `occursIn` (#12) already removes the repeated walks, and a static
  decision would need to know which head-bound subterms are ground at call
  time.
- Pre-existing difference from SWI-Prolog: `assert`/`retract` inside
  `findall` are undone when findall backtracks, and `retract` of a consulted
  (non-asserted) fact fails. SWI keeps both changes (logical update view).
