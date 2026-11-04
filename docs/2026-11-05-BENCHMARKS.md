# Benchmarks by task type, JIT on and off - 2026-11-05

Kind: measurement report. Follows
[`2026-11-04-NEXT-HORIZONS.md`](2026-11-04-NEXT-HORIZONS.md) (the JIT
repaired so its kernels run) and
[`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md) (Horizon
2 pruning removed, arithmetic guard prefixes). Earlier comparable figures:
[`2026-10-30-JIT-ACTIVATION.md`](2026-10-30-JIT-ACTIVATION.md) (in-process,
same method) and
[`2026-11-01-INFERA-PERF-RESULTS.md`](2026-11-01-INFERA-PERF-RESULTS.md)
(whole process, but on a Linux x86-64 VM).

## Setup

| | |
| --- | --- |
| Revision | `ce07b82` (`main`), clean tree |
| Build | GHC 9.8.2, `cabal build exe:infera bench:core-major --enable-benchmarks --enable-optimization=2` in a separate build directory |
| Host | Apple M4 (4 performance + 6 efficiency cores), 16 GiB, macOS 27.2 |
| Load | about two cores busy with unrelated processes (`mediaanalysisd`, an editor helper) throughout |
| Other systems | SWI-Prolog 10.0.2, Scryer 0.10.0 |
| JIT | `INFERA_JIT=1` (default) and `INFERA_JIT=0`, same binary |

**Whole process** (`bench/run.py`): CLI startup, loading, solving and
output; 1 warmup and 5 timed runs per engine and case; every run validated
by the harness (one correct result and completion marker). Figures are
medians.

**In process** (`core-major --case C --batch 20 +RTS -T -RTS`): per-query
CPU time and GHC allocation of a loaded, checked program, with source
loading, the Reference oracle and the Core preflight excluded; every record
reports `status: ok`, `oracle_checked`, `independent_checked` and
`fully_drained`. Three samples per mode, interleaved JIT on and off, as in
the JIT activation report; figures are medians. The allocation figure
includes a fixed share of RTS bookkeeping (about 8.5 MB), so compare
differences, not ratios.

Raw records:
[`data/jsonl/engine-benchmarks-cli-2026-11-05.jsonl`](data/jsonl/engine-benchmarks-cli-2026-11-05.jsonl),
[`data/jsonl/engine-benchmarks-major-2026-11-05.jsonl`](data/jsonl/engine-benchmarks-major-2026-11-05.jsonl);
summary:
[`data/tsv/engine-benchmarks-2026-11-05.tsv`](data/tsv/engine-benchmarks-2026-11-05.tsv).

## Against other Prologs (whole process)

| Task type | Case | Infera JIT on | Infera JIT off | SWI-Prolog | Scryer | JIT on / SWI | spread (JIT on) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| List building | nrev | 46.8 ms | 222.3 ms | 52.0 ms | 141.7 ms | 0.90x | 11% |
| Integer loop | loop | 20.5 ms | 35.9 ms | 18.1 ms | 59.3 ms | 1.13x | 20% |
| Backtracking search | queens | 20.0 ms | 35.4 ms | 19.0 ms | 56.4 ms | 1.05x | 68% |
| Deep recursion, untabled | fib | 58.4 ms | 50.7 ms | 48.3 ms | 79.5 ms | 1.21x | 20% |
| Arithmetic | primes | 605.9 ms | 601.6 ms | 306.2 ms | 586.9 ms | 1.98x | 1% |
| Puzzle unification | zebra | 670.5 ms | 679.2 ms | 162.7 ms | 626.0 ms | 4.12x | 2% |
| Symbolic terms | deriv | 452.3 ms | 457.7 ms | 92.9 ms | 336.4 ms | 4.87x | 3% |

Spread is (max - min) / median over the five runs. nrev, loop and queens
finish in 20-50 ms, so startup is a large part of them, and fib's JIT on/off
difference is inside its 20% spread: fib has no native kernel.

## Inside the engine

| Task type | Case | JIT on ms/query | JIT off ms/query | JIT speedup | alloc MB/query on / off |
| --- | --- | ---: | ---: | ---: | ---: |
| Integer loop | core-loop | 0.064 | 8.135 | 127x | 8.57 / 23.69 |
| Loop over reused slots | liveness | 0.325 | 10.984 | 34x | 10.54 / 31.26 |
| List building | core-nrev | 0.781 | 6.708 | 8.6x | 10.18 / 16.47 |
| Backtracking search | core-queens | 3.356 | 7.015 | 2.1x | 15.11 / 22.99 |
| Deep recursion | core-fib | 32.323 | 32.332 | 1.0x | 93.95 / 93.95 |
| Constraint puzzles | example-sudoku4 | 15.672 | 15.628 | 1.0x | 85.12 / 85.19 |
| | minefield-16 | 21.903 | 21.366 | 1.0x | 117.53 / 117.13 |
| Circuit layout (CLP) | breadboard-rc | 0.710 | 0.704 | 1.0x | 12.52 / 12.52 |
| | breadboard-div | 1.768 | 1.796 | 1.0x | 14.66 / 14.66 |
| | breadboard-tri | 3.461 | 3.443 | 1.0x | 24.63 / 24.63 |
| | breadboard-wide | 9.959 | 9.939 | 1.0x | 51.10 / 51.10 |
| Planning and scheduling | example-river | 0.139 | 0.139 | 1.0x | 8.88 / 8.88 |
| | example-job-shop | 0.230 | 0.231 | 1.0x | 9.62 / 9.62 |
| | example-routes | 0.042 | 0.043 | 1.0x | 8.65 / 8.65 |
| | example-packing | 0.525 | 0.530 | 1.0x | 11.00 / 11.00 |
| Control and indexing | controls | 0.122 | 0.122 | 1.0x | 9.13 / 9.13 |
| | guards | 1.895 | 1.899 | 1.0x | 18.49 / 18.49 |
| | deep-index | 2.543 | 2.543 | 1.0x | 19.49 / 19.49 |
| Tabling | table-cycle | 0.055 | 0.056 | 1.0x | 8.82 / 8.82 |
| | table-cycle240 | 0.934 | 0.929 | 1.0x | 13.79 / 13.79 |

Spreads are at most 7% for JIT on and 11% for JIT off (table-cycle, the
shortest case); most are 0-4%.

## Reading

- **Native code helps where it applies, and only there.** Loops, list
  building and the queens safety check (the `safe`/`noatt` kernel) run
  2-127x faster with the JIT. Constraint puzzles, planning, tabling, deep
  non-tail recursion and unification-heavy search run entirely in the
  interpreter, so the JIT changes nothing for them.
- **The general clause compiler (Horizons 1 and 4) adds no speed of its own
  on these workloads.** It now compiles the countdown loop, which the
  removed hand-written countdown kernel used to handle, at the same 0.064 ms;
  the other gains come from the `nrev` and `safe` kernels that predate it.
  For zebra, deriv and primes the JIT declines every predicate (see the
  unification-heavy report); the example programs show no JIT difference
  either.
- **No regression from the 2026-11-04 repairs.** Against the JIT activation
  report (same method, 2026-10-30): core-nrev 0.867 -> 0.781 ms, core-queens
  3.514 -> 3.356 ms, core-loop 0.064 -> 0.064 ms, core-fib 31.836 -> 32.323 ms.
- **Unification-heavy programs are the largest gap**: zebra and deriv are
  4-5x behind SWI-Prolog and about level with Scryer; primes is 2x. The
  ranked plan for them is in
  [`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md),
  whose own figures (zebra 0.65 s, deriv 0.44 s, primes 0.63 s user time)
  agree with these.
- **Not comparable with the 2026-11-01 ratios**: that comparison ran on a
  noisy Linux x86-64 VM, where SWI-Prolog was relatively slower (for example
  nrev 0.39x there, 0.90x here).

## Not measured

- x86-64: CI runs the JIT natively on Linux (green at `c259cdb`), but there
  is no x86-64 timing in this report.
- gprolog and Trealla are not installed on this host.
- Allocation in the whole-process runs, and cold loading/compilation as a
  separate figure.
