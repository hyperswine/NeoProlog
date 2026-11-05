# Benchmarks after the list kernels, and a unify regression - 2026-11-05

Kind: measurement report and a small engine fix. Repeats
[`2026-11-05-BENCHMARKS.md`](2026-11-05-BENCHMARKS.md) (this morning, at
`ce07b82`) after the per-call work, the list-search kernel and the list
filter kernel merged
([`PER-CALL-WORK`](2026-11-05-PER-CALL-WORK.md),
[`SCAN-KERNEL`](2026-11-05-SCAN-KERNEL.md),
[`FILTER-KERNEL`](2026-11-05-FILTER-KERNEL.md)). Measuring found a
regression from the per-call work, fixed here first; the tables are for the
fixed build.

## Setup

| | |
| --- | --- |
| Revision | `main` at `cedb709`, plus the fix below |
| Build | GHC 9.8.2, `--enable-optimization=2 --enable-benchmarks`, fresh build directory |
| Host | Apple M4, 16 GiB, macOS 27.2; load average about 4 throughout |
| Other systems | SWI-Prolog 10.0.2, Scryer 0.10.0 (measured in the same session, half an hour earlier) |
| Method | as this morning: `bench/run.py` (whole process, 1 warmup, 5 timed runs, every run validated) and `core-major --case C --batch 20` (in process, 3 samples per mode, JIT on and off interleaved, every record `ok`, oracle-checked, independently checked and fully drained); medians |

Raw records:
[`data/jsonl/engine-benchmarks-cli-2026-11-05-evening.jsonl`](data/jsonl/engine-benchmarks-cli-2026-11-05-evening.jsonl),
[`data/jsonl/engine-benchmarks-major-2026-11-05-evening.jsonl`](data/jsonl/engine-benchmarks-major-2026-11-05-evening.jsonl);
summary:
[`data/tsv/engine-benchmarks-2026-11-05-evening.tsv`](data/tsv/engine-benchmarks-2026-11-05-evening.tsv).

## Against other Prologs (whole process)

| Task type | Case | Infera JIT on | JIT off | SWI-Prolog | Scryer | on / SWI | this morning on / SWI |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Arithmetic and lists | primes | 63.9 ms | 575.0 ms | 321.7 ms | 611.5 ms | **0.20x** | 1.98x |
| List building | nrev | 35.7 ms | 166.1 ms | 53.3 ms | 143.8 ms | 0.67x | 0.90x |
| Deep recursion, untabled | fib | 50.8 ms | 50.9 ms | 56.0 ms | 83.1 ms | 0.91x | 1.21x |
| Backtracking search | queens | 20.5 ms | 20.5 ms | 20.2 ms | 58.8 ms | 1.02x | 1.05x |
| Integer loop | loop | 20.4 ms | 35.7 ms | 19.6 ms | 61.2 ms | 1.04x | 1.13x |
| Puzzle unification | zebra | 215.2 ms | 603.1 ms | 170.3 ms | 636.5 ms | **1.26x** | 4.12x |
| Symbolic terms | deriv | 399.9 ms | 407.3 ms | 95.4 ms | 343.3 ms | 4.19x | 4.87x |

nrev, loop, queens and fib finish in 20-60 ms, most of which is process
startup and loading, and SWI-Prolog's own figures moved by up to 15% between
this morning and now (fib 48.3 -> 56.0 ms), so their ratios are rough. loop's
spread was 24%; the others' at most 9%.

Infera is now ahead of Scryer on every case but deriv (400 against 343 ms)
and ahead of SWI-Prolog on primes (5x) and nrev. zebra is within 30% of SWI-Prolog. deriv is the one
large gap left: no native kernel applies to it (it builds nested terms in
non-tail double recursion), and the interpreter's per-call cost is still
3-9x SWI-Prolog's (see `PER-CALL-WORK`).

## Inside the engine

Per-query CPU time and GHC allocation (in process):

| Task type | Case | JIT on ms | JIT off ms | JIT speedup | alloc MB on / off | on vs this morning |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Integer loop | core-loop | 0.063 | 7.154 | 114x | 8.57 / 20.81 | 0.98 |
| Loop over reused slots | liveness | 0.330 | 10.032 | 30x | 11.06 / 28.26 | 1.02 |
| List building | core-nrev | 0.656 | 4.991 | 7.6x | 9.68 / 14.56 | 0.84 |
| Backtracking search | core-queens | 2.996 | 6.375 | 2.1x | 12.98 / 19.47 | 0.89 |
| Deep recursion | core-fib | 31.517 | 31.439 | 1.0x | 82.30 / 82.30 | 0.98 |
| Constraint puzzles | example-sudoku4 | 15.722 | 15.665 | 1.0x | 85.12 / 85.18 | 1.00 |
| | minefield-16 | 21.247 | 21.138 | 1.0x | 116.96 / 116.56 | 0.97 |
| Circuit layout (CLP) | breadboard-rc | 0.667 | 0.658 | 1.0x | 12.50 / 12.50 | 0.94 |
| | breadboard-div | 1.638 | 1.638 | 1.0x | 14.62 / 14.62 | 0.93 |
| | breadboard-tri | 3.232 | 3.239 | 1.0x | 24.53 / 24.52 | 0.93 |
| | breadboard-wide | 9.430 | 9.494 | 1.0x | 51.07 / 51.07 | 0.95 |
| Planning and scheduling | example-river | 0.131 | 0.141 | 1.1x | 8.83 / 8.83 | 0.95 |
| | example-job-shop | 0.233 | 0.233 | 1.0x | 9.62 / 9.62 | 1.01 |
| | example-routes | 0.037 | 0.041 | 1.1x | 8.64 / 8.64 | 0.87 |
| | example-packing | 0.526 | 0.530 | 1.0x | 11.00 / 11.00 | 1.00 |
| Control and indexing | controls | 0.110 | 0.110 | 1.0x | 9.01 / 9.01 | 0.90 |
| | guards | 1.873 | 1.893 | 1.0x | 18.17 / 18.17 | 0.99 |
| | deep-index | 2.371 | 2.334 | 1.0x | 15.29 / 15.29 | 0.93 |
| Tabling | table-cycle | 0.054 | 0.054 | 1.0x | 8.82 / 8.82 | 0.99 |
| | table-cycle240 | 0.891 | 0.888 | 1.0x | 13.79 / 13.79 | 0.95 |

Spreads are at most 5%. These cases contain no list searches or filters,
so the two kernels do not appear here; the gains (5-16% on nrev, queens,
controls, indexing and the CLP layouts) are the per-call work. Constraint
solving, planning and tabling still run entirely in the interpreter.

## The regression: helpers lifted out of `unify` and the occurs walk

Measuring `main` as merged showed two cases worse than this morning, both
bisected to `2d4e747` (the per-call work):

| case | this morning | `main` | fixed |
| --- | ---: | ---: | ---: |
| liveness, JIT on | 0.325 ms | 0.466 ms | 0.330 ms |
| core-fib | 32.3 ms, 94.0 MB | 33.3 ms, 121.1 MB | 31.5 ms, 82.3 MB |

That commit moved `unify`'s `bindChecked` and argument loop, and the occurs
walk's argument loop, from local definitions to top-level functions with
strict arguments, meaning to stop GHC boxing the address on every bind. The
measurement then covered zebra, deriv, primes, queens and nrev only. The
lifted versions allocate instead: `unify` became 32% of fib's allocation
(late cost-centre profile), and the mutually recursive `occursWalk` /
`occursArgs` cost about 24 bytes per list cell, which liveness pays on
`id Junk _`, an occurs check over a 20000-element list. Both are back as
local definitions (`Store.unify`, `Store.occursWalk`).

Instructions retired, millions, `main` against the fix:

| case | `main` | fixed |
| --- | ---: | ---: |
| zebra x300 | 4217 | 4215 |
| deriv x30000 | 9787 | 9718 |
| primes 20000 | 1383 | 1379 |
| queens 9, all | 9325 | 9204 |
| nrev 30 x 30000 | 5063 | 5005 |

No case is worse. Full `cabal test all`, core-engine parity over
`test/core/*.nprolog` in all four modes, and every CI script pass.

## Cheaper choice points: measured, not done

Every choice point saves four pieces of branch state (tables, dynamic
facts, the constraint mark, the watched set) and every backtrack restores
them, even for pure programs that never change them. A throwaway build that
skipped the table, dynamic-fact and watched-set copies entirely, which is
correct only for pure programs, bounds what a version counter could save:
zebra 4230M -> 4137M instructions (-2.2%), queens 9352M -> 9154M (-2.1%),
primes and nrev unchanged. deriv could not be measured that way, because
collection reads those slots. A real version counter would recover part of
the 2% and would need the collector and the constraint-store marks to
follow it, so it is not worth doing now.

## Not measured

- x86-64 timing (CI runs the JIT there; no timing).
- gprolog and Trealla (not installed).
- Constraint, planning and tabling workloads against other systems: the
  in-process cases have no SWI-Prolog or Scryer versions.
