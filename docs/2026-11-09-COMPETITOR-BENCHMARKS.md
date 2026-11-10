# Infera against other Prologs on linux x86-64 - 2026-11-09

Kind: measurement report. Whole-process timings of Infera at `9a93cfe` (2.5.0 + 2) against SWI-Prolog, GNU Prolog, Trealla and Scryer on one shared, noisy Linux x86-64 VM. No engine change. Jack's macOS arm64 machine was **not** measured in the original Nov 9 pass (see Addenda 1 & 2 below for macOS arm64 measurements through `84812e8`).

**Short answer (Nov 9 at `9a93cfe`):** Current Infera (main `9a93cfe`, 2.5.0 + 2 commits) wins clearly on the shapes its JIT kernels cover: startup, nrev, primes, zebra, and the repo's `bench_deriv`, where the derivative is thrown away. It also beats SWI (but not gprolog) on untabled tak and fib. It is still about 2–3× behind SWI on findall, assert, first-argument indexing, and symbolic term work when the result is actually used (the findall row's 4.5× is overstated by a harness artifact; see the correction below). It also gives a wrong answer on `deriv` with `plus`/`minus` constructors. Infera wins 5 of 12 suite rows outright and beats SWI on 7 of 12. The "big wins" depend on kernels that apply only to specific clause shapes.

**Update (Nov 10 at `84812e8` on macOS arm64 — see Addendum 2):** With Tracks 1–5 implemented, Infera beats Scryer Prolog 0.10.0 across **all 13 competitor workloads** (`1.5×` to `16.5×` faster) and flips every major bottleneck from the Nov 9 report (`tak`, `fib`, `queens`, `derivrkeep`, `derivracc2`, `assertz`, and `findall`).

## What was measured

| | |
|---|---|
| Infera | `NeoProlog` main **`9a93cfe891523c4bc439efc5ff74d9dee74e690c`** (2026-11-08 23:50 AEDT), `git describe` = `v2.5.0-2-g9a93cfe`; `infera --version` = 2.5.0. The 2 commits after the tag add examples and a readability edit (`705c13d` also adds "compact clause-JIT helpers"). |
| Build | built from source at that commit. `cabal build exe:infera -w ghc-9.8.2 --enable-optimization=2 --enable-benchmarks` (the CI flags and GHC version). Linked against the system libgmp/libtinfo through `LIBRARY_PATH` symlinks (the box has no `-dev` packages). Binary sha256 prefix `60dd876ba765636f`. Run as `infera FILE +RTS -N1 -RTS` with `:q` on stdin. |
| SWI-Prolog | 10.0.0 (conda-forge); same install as the 2026-11-01 report |
| GNU Prolog | 1.6.0, git master `55fd5878` (2026-10-20), built from source. **Consulted (bytecode), not `gplc` native.** `LOCALSZ`/`GLOBALSZ`=4000000, `TRAILSZ`=2000000 |
| Trealla | v3.14.62, git `efdabe0` (2026-11-09), built from source. **Not** the Nov 1 build (git 4e76). That build was gone, so Trealla ratios are not strictly comparable with Nov 1. |
| Scryer | 0.10.0 (cargo); same as the 2026-11-01 report |
| Host | shared VM: 8 vCPU "Intel Xeon Processor", 15 GiB, Debian 13 (glibc 2.41), kernel 6.12.113. Load average about 1 during runs. Not macOS: no arm64 or macOS JIT numbers here. |
| Method | whole-process wall clock (startup + load + solve + print). Per program: 1 warm-up round, then 5 timed rounds, interleaved across all systems in each round. The cell is the **median of 5**. Every run's printed answer was recorded. Extra deriv variants (`*keep`, `racc2`): median of 3. Main pass 17:49–18:07 AEDT and deriv variants about 18:08 AEDT on 9 Nov; probes after that. |
| Infera modes | **Primary: tabling OFF (`<- notable.` header), JIT ON.** Also JIT off (`INFERA_JIT=0`) and default (as written, auto-tabling on). |

### Workloads rebuilt, not reused

The benchmark workspace used for [`2026-11-01-INFERA-PERF-RESULTS`](2026-11-01-INFERA-PERF-RESULTS.md) (its `run.py`, `progs/` and raw samples, kept outside the repo) was no longer on the VM, and neither were its gprolog and Trealla builds. The suite was **rebuilt** from two sources:
- the workload descriptions in `docs/2026-11-01-INFERA-PERF-RESULTS.md`
- the repo's `bench/bench.pl` / `bench.nprolog` (nrev, fib, queens, zebra, deriv, primes come verbatim from there)

The generator, runner, programs and raw JSONL samples are kept outside the repo, in the benchmark workspace (see Reproducing).

- Same as Nov 1 (SWI times match within noise): hello, nrev30×30000, tak(24,16,8), 9-queens all solutions, fib(27), assertz 100k + findall + sum.
- **Probably not the same workload** as Nov 1/Nov 4 (SWI's own time moved a lot):
  - zebra: SWI 0.55 → 0.26 s
  - deriv: SWI 1.06 → 0.15 s
  - primes: SWI 0.28 → 0.49 s
  - findall 50k: SWI 0.10 → 0.02 s

  For these rows, compare **ratios** with the earlier numbers only loosely.
- The deriv answer check is now the total node count of the 4 derivatives (377 correct, 375 with plus/minus). The earlier 407/405 metric was not recoverable; the 2-node gap is the same bug.
- `findall` = `findall(X, btw(1,50000,X), L)` with a user `btw/3` counter generator. `index` = 2000 static `k/2` facts, each looked up by first argument, 20 rounds.

## Results (seconds, median; lower is better)

| program | answer (Infera / SWI) | Infera (tabling off, JIT on) | Infera JIT off | Infera default (tabling on) | SWI 10.0.0 | gprolog 1.6.0 (consult) | Trealla v3.14.62 | Scryer 0.10.0 | Infera ÷ SWI | Infera ÷ best other | fastest |
|---|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|---|
| hello | hello | 0.004 | 0.004 | 0.004 | 0.009 | 0.007 | 0.024 | 0.073 | 0.49× | 0.57× (gprolog) | Infera |
| nrev | 30 | 0.088 | 1.836 | 0.088 | 0.971 | 0.693 | 3.860 | 1.264 | 0.09× | 0.13× (gprolog) | Infera |
| tak | 9 | 0.577 | 0.538 | 0.018 | 1.626 | 0.490 | 1.380 | 0.515 | 0.35× | 1.18× (gprolog) | gprolog |
| fib | 196418 | 0.149 | 0.123 | 0.020 | 0.382 | 0.123 | 0.256 | 0.184 | 0.39× | 1.21× (gprolog) | gprolog |
| queens | 352 | 0.619 | 1.146 | 0.619 | 0.539 | 0.637 | 1.338 | 0.928 | 1.15× | 1.15× (swipl) | swipl |
| primes | 2262 | 0.109 | 0.695 | 0.110 | 0.489 | 0.481 | 1.342 | 0.710 | 0.22× | 0.23× (gprolog) | Infera |
| zebra | japanese | 0.146 | 0.687 | 0.145 | 0.257 | 0.286 | 0.838 | 0.696 | 0.57× | 0.57× (swipl) | Infera |
| zebra3k | japanese | 1.233 | 6.428 | 1.251 | 2.450 | 2.643 | 8.038 | 6.282 | 0.50× | 0.50× (swipl) | Infera |
| derivr | 377 | 0.113 | 0.555 | 0.116 | 0.152 | 0.228 | 0.561 | 0.433 | 0.74× | 0.74× (swipl) | Infera |
| derivr300k | 377 | 0.410 | 4.980 | 0.389 | 1.473 | 2.238 | 5.728 | 3.677 | 0.28× | 0.28× (swipl) | Infera |
| derivrkeep | 30000 | 0.263 | 0.596 | — | 0.150 | 0.240 | — | — | 1.76× | 1.76× (swipl) | swipl |
| derivracc | 11310000 | 3.647 | 3.643 | 3.708 | 2.079 | 2.640 | 13.084 | 8.224 | 1.75× | 1.75× (swipl) | swipl |
| derivracc2 | 11310000 | 3.753 | 3.714 | — | 1.241 | 1.568 | — | — | 3.03× | 3.03× (swipl) | swipl |
| deriv | **375 / 377** | 0.660 | 0.743 | 0.670 | 0.153 | 0.236 | 0.544 | 0.430 | 4.32× | 4.32× (swipl) | swipl |
| derivkeep | 30000 | 0.720 | 0.794 | — | 0.147 | 0.254 | — | — | 4.91× | 4.91× (swipl) | swipl |
| derivacc | **11250000 / 11310000** | 9.370 | 9.288 | 9.451 | 2.134 | 2.764 | 13.607 | 8.441 | 4.39× | 4.39× (swipl) | swipl |
| assertz | 5000050000 | 0.139 | 0.154 | 0.139 | 0.050 | 0.064 | 0.146 | 0.589 | 2.77× | 2.77× (swipl) | swipl |
| findall | 1250025000 | 0.091 | 0.098 | 0.089 | 0.020 | 0.021 | 0.054 | 0.090 | 4.51× | 4.51× (swipl) | swipl |
| index | 200432520 | 0.056 | 0.056 | 0.056 | 0.028 | 0.035 | 0.052 | 0.110 | 2.05× | 2.05× (swipl) | swipl |


Rows `zebra3k`, `derivr300k`, `derivrkeep`, `derivracc`, `derivracc2`, `derivkeep`, `derivacc` are validation variants added for this report:
- **zebra3k / derivr300k**: 10× the iterations, to check the wins scale and are not startup artefacts. They do scale.
- **derivrkeep / derivkeep**: same deriv loop, but the 4 derivatives are returned and inspected (`\+ D == 0`) each iteration, not bound to `_`.
- **derivracc**: also computes each derivative's size every iteration (Prolog side uses `=..`; Infera uses per-constructor clauses).
- **derivracc2**: like derivracc, but both sides use the *same* per-constructor size clauses (fairest).

## Who wins what

Primary rows (one per workload: hello, nrev, tak, fib, queens, primes, zebra, derivr, deriv, assertz, findall, index):
- **Infera fastest overall:** startup (4 ms), nrev (11× faster than SWI, 8× faster than gprolog), primes (4.5× faster than SWI), zebra (about 2× faster than SWI; holds at 3000 iterations), and the repo's derivr (0.74×; 0.28× at 300k iterations).
- **Infera beats SWI but not gprolog bytecode:** tak (0.35× SWI, 1.18× gprolog), fib 27 (0.39× SWI, 1.21× gprolog). SWI is the slowest system on these two, which flatters the ratio.
- **Infera loses:**
  - queens 1.15× SWI (level with gprolog)
  - first-argument indexing 2.0× SWI
  - assertz 2.8×
  - findall 4.5× as measured, about 2.1× once the harness artifact is removed (see correction)
  - deriv with `plus`/`minus` 4.3×, **and the answer is wrong**
- **Symbolic terms when the result is used:** derivrkeep 1.76× SWI, derivracc 1.75×, derivracc2 3.0×. The repo's `bench_deriv` binds every derivative to `_`. Its JIT win (0.11 s vs JIT-off 0.56 s) disappears once the derivative is returned and inspected (0.26 s), and completely once it is walked (JIT on = JIT off = 3.6 s). So the headline deriv win measures a case where no output term is consumed, not general structure building.
- **vs Scryer and Trealla:** Infera is faster than both on every row except index (Trealla 0.052 vs 0.056, a tie), findall (Scryer tie) and the plus/minus deriv rows.

## JIT on vs off; default tabling

- **Answers agree** between JIT on, JIT off and default on every suite program and on the deep-loop checks.
- **The JIT helps:** nrev (21×), zebra (4.7×), primes (6.4×), queens (1.9×), and the repo's discarded-result deriv (4.9×).
- **The JIT is slower on fib and tak on x86-64.** fib 0.149 s on vs 0.123 off; tak 0.577 vs 0.538.
  - `INFERA_JIT_DEBUG=1` shows the new clause unit is compiled for `fib/2` and `tak/4` and then hits **`heap limit -> interpreter`**, rerunning on the interpreter.
  - `INFERA_JIT_CLAUSES=0` gives fib 0.121–0.125 s and tak 0.50–0.53 s; that is the wasted work.
  - fib(20) stays native. This contradicts `docs/2026-11-06-CLAUSE-UNITS.md`'s "fib 25 −79% instructions", which was measured on aarch64-darwin only. On this x86-64 box, at fib 27, the clause unit costs about 20%.
- **Default (auto-tabling on):**
  - Still memoises tak and fib (0.018 s / 0.020 s). Those rows measure tabling, not execution, and are not comparable.
  - Everything else matches tabling-off times and answers. nrev (0.088 s) and findall (0.089 s) are no longer quadratic or timing out, so the Nov 1 tabling distortions on nrev, findall and assert are fixed.

## Correctness issues still present

1. **Arithmetic functors as data (issue #7, closed 4 Nov as documented behaviour plus a lint).**
   - Ground `plus`/`minus` arguments are still evaluated before head matching, so deriv with `plus`/`minus` gives **375 vs 377** (accumulated: 11,250,000 vs 11,310,000).
   - The same program is also 4.3–4.9× slower than SWI.
   - Answer printing evaluates too: `T = 5 - 2, T = A - B` answers `T = 3, A = 5, B = 2`.
2. **Occurs check is always on:** `X = f X` → `false.` SWI succeeds (creates a cyclic term). ISO leaves this undefined, but programs ported from SWI can behave differently.
3. **Hard depth limit of about 100,000 non-tail calls.**
   - `count 99999` works, `count 100000` reports "Search depth limit reached; the query was not proven false." The same happens for `len` of a 1,000,000-element list.
   - JIT on and off agree.
   - SWI handles 1,000,000 (default 1 GB stack). Tail loops are fine (`loop 10000000` → true).
4. `length/2` is not available in the CLI here ("unknown predicate: length/2"); the suite uses a user `len/2`. (Scryer also needs `library(lists)` for `length`.)
5. Not an Infera bug, but it affects the nrev ratio: `bench_nrev` without cuts leaves a `range/3` choice point per iteration in SWI. At 300,000 iterations SWI ran out of its 1 GB stack after 140 s, while Infera took 0.66–0.80 s. Infera's determinism inference removes those choice points; part of the 11× nrev gap is that, not raw speed.

## Compared with Nov 1 (2.2.0/main) and Nov 4–5

| program | Nov 1 Infera×SWI | Nov 4–5 Infera / SWI (s) | today Infera / SWI (s) | today ×SWI |
|---|---|---|---|---|
| startup | ~0.5× | – | 0.004 / 0.009 | 0.49× |
| nrev | 0.39× | 0.40 / 1.02 | 0.088 / 0.971 | 0.09× |
| tak (untabled) | 0.38× | 0.69 / 1.52 | 0.577 / 1.626 | 0.35× |
| fib 27 (untabled) | 0.35× | – | 0.149 / 0.382 | 0.39× |
| queens 9 | 1.10× | 0.66 / 0.55 | 0.619 / 0.539 | 1.15× |
| primes | 3.6× | 1.12 / 0.28 | 0.109 / 0.489* | 0.22× |
| zebra | 3.6× | 2.17 / 0.55 | 0.146 / 0.257* | 0.57× |
| deriv renamed | 2.85× | 3.34 / 1.07 | 0.113 / 0.152* (result discarded); 0.263 / 0.150 (result kept) | 0.74× / 1.76× |
| deriv plus/minus | wrong (405) | 11.1 / 1.12 | 0.660 / 0.153*, wrong (375) | 4.3× |
| assertz 100k | 3.06× (main) | – | 0.139 / 0.050 | 2.8× |
| findall 50k | – | 0.57 / 0.10 | 0.091 / 0.020* | 4.5× |
| first-arg index 2000 | – | 1.13 / 0.057 | 0.056 / 0.028 | 2.0× |

\* SWI's own time differs a lot from the earlier run, so the rebuilt workload is probably not identical; read the trend, not the exact ratio.

**Trend:**
- Large real gains since Nov 4: the list-search/filter kernels took primes and zebra from about 3.6× behind SWI to ahead of it, and nrev roughly 4.5× faster.
- Indexing improved a lot in absolute terms (1.13 s → 0.056 s).
- Unchanged: queens, tak and fib ratios; assert still about 3× behind and findall about 2× (4.5× as first measured, see correction); general symbolic term building still about 1.75–3× behind when the output is used.

## Repo performance claims vs measured here

- `docs/2026-11-05-BENCHMARKS-EVENING.md` (Apple M4, smaller sizes) claims primes 0.20× SWI, nrev 0.67×, fib 0.91×, queens 1.02×, zebra 1.26×, deriv 4.19×.
  - Here (x86-64, larger sizes): primes 0.22× (matches), nrev 0.09× (better), queens 1.15× (roughly matches).
  - zebra 0.57×: better than claimed, after the later kernels.
  - fib 0.39× untabled: better, but SWI is slow on this box and the JIT makes fib *worse* here.
- `docs/2026-11-06-CLAUSE-UNITS.md` claims fib 25 −79% instructions from clause units (aarch64-darwin). **Not reproduced on x86-64 at fib 27**: the unit hits its heap limit and falls back, about 20% slower than with clause units off.
- 2.5.0 / `89aab70` ("clause compiler increment 2") targets d/3 choice points, and the design doc's gate is "deriv within 1.5× of SWI". The repo's bench_deriv passes that gate here (0.74×) only because its outputs are discarded. With outputs kept it is 1.76×; walked with identical code, 3.0×.
- Earlier docs (`2026-10-15-PERFORMANCE.md`, `2026-10-30-JIT-ACTIVATION.md`) report in-process loaded-query times on the author's machine. As on Nov 1, they exclude startup and are not whole-process comparisons.

## Caveats

- Noisy shared VM: most rows spread ±5–10% (min/max per sample are in the JSONL). Rows under about 60 ms (hello, index, findall for SWI/gprolog) are dominated by startup and loading.
- Whole-process times only; no exclude-startup measurement in this pass.
- gprolog is consulted bytecode; native `gplc` would be faster.
- Trealla is a newer build than Nov 1.
- One program per system, no cuts, same algorithm. Each Infera file carries the full bench predicate set (same as the repo file); Prolog files likewise.
- x86-64 JIT only. The macOS/arm64 JIT backend may behave differently, especially the clause-unit fallback.

## Reproducing

1. Build as above: `cabal build exe:infera -w ghc-9.8.2 --enable-optimization=2 --enable-benchmarks`.
2. Write one plain translation per system:
   - nrev, fib, queens, zebra, deriv and primes come from `bench/bench.pl` / `bench/bench.nprolog`, with the sizes in the table.
   - Each Infera file starts with `<- notable.` for the primary column; the default column uses the same file without that line.
   - Each Prolog file defines `main/0`, which prints the answer.
3. Time each process from start to exit:
   - `swipl -q -g main -t halt F.pl`
   - `gprolog --init-goal "consult('F.pl'),main,halt"`
   - `tpl -q F.pl -g main,halt`
   - `scryer-prolog -g main,halt F.pl`
   - `infera F.nprolog +RTS -N1 -RTS` with `:q` on stdin; `INFERA_JIT=0` for the JIT-off column
4. Run 1 warm-up and 5 timed rounds, interleaved across systems. Check every printed answer and take the median.
5. Probes: `INFERA_JIT_DEBUG=1` shows the clause-unit fallback; `INFERA_JIT_CLAUSES=0` turns clause units off.

## Correction (2026-11-09, later the same day): findall harness artifact

The `findall` query in the rebuilt harness was not wrapped in `once`, so Infera's REPL also printed the whole 50k-element list `L` (about 339 KB of stdout) while SWI and gprolog printed only the sum. That inflated Infera's findall time. With the same query wrapped in `once` (prints only the sum), interleaved median of 5 at `9a93cfe`: Infera 0.040 s vs SWI 0.019 s, about **2.1×**, not 4.5×. The assertz and index queries were already `once`-wrapped and are unaffected. The table rows above are left as originally measured.

## Addendum (2026-11-10): Follow-Up Fixes for Clause-Unit Heap Reclamation, Native Choice Enumeration, and Arg-0 Indexing

Following this report, three targeted engine and clause-JIT updates were landed on macOS arm64 (Apple M4):

1. **Functor-Free Heap Reclamation (`unitCanReclaimH` in `Clause.hs`)**:
   - Previously, `fib/2` and `tak/4` allocated body-local `tagRef` cells on the native heap (`F1, F2` in `fib`, `A1, A2, A3` in `tak`) without reclaiming them on clause return, exhausting the native heap at `fib(27)` and `tak(24,16,8)` and falling back to the interpreter (`heap limit -> interpreter`).
   - Exclusive functor-free clause units now snapshot and restore the heap pointer `H` across non-tail calls and before tail/return exits after dereferencing output registers, eliminating the fallback completely.
2. **Rerun-Free Native Choice Enumeration (`upRerunFree` & `drainNativeFindAll` in `Clause.hs`, `Jit.hs`, `Run.hs`)**:
   - Statically proves when a compiled clause unit cannot return `jitStatusRerun` for well-moded entry calls (`inferChoiceNeeds`), enabling `allowChoices = True` for top-level `CDone`, `CExitFindAll`, and `CExitMinimize` continuations, plus a tight `drainNativeFindAll` loop and in-place `AltNative` mark updates.
3. **Raised Clause Cap (128), Grouped Arg-0 Binary Search (`arg0ConstGroups`), Tightened `isTrmcCallee`, Mode-Specialized Head Codegen, & 0-Var Ground Fact Fast Path**:
   - Raises `admitClauseUnit` to 128 clauses, emits a binary-search dispatch tree on argument 0 for predicates (`arity >= 2`) with `>= 4` constant groups (e.g., 112-clause `knight_edge/2`), tightens `isTrmcCallee` so `absent/2` and `bulls/6` inline into callers' native units, shrinks `unifyWords` call sites from 31 to 7 AArch64 instructions, and skips `allocFrame` on 0-variable ground facts.

### macOS arm64 Before/After (`<- notable.`, median of 5, whole-process wall clock)

| Workload | Native Unit Size | `JIT=0` (s) | `JIT=1` Before (s) | `JIT=1` After (s) | Speedup (`JIT=0 ÷ JIT=1`) | Notes |
|---|---:|---:|---:|---:|---:|---|
| `fib(27)` | 3,800 B | 0.106 | 0.137 (fallback) | **0.020** | **5.31×** | 0 heap fallbacks |
| `tak(24, 16, 8)` | 4,296 B | 0.403 | 0.471 (fallback) | **0.032** | **12.59×** | 0 heap fallbacks |
| `findall_50k` (`once`-wrapped) | 2,160 B | 0.044 | 0.044 | **0.020** | **2.15×** | Native `drainNativeFindAll` |
| `peg_solitaire` (20× `peg_solution_count`) | 35,400 B | 0.032 | 0.032 | **0.016** | **1.97×** | Code size −48.5% (from 68,780 B) |
| `mastermind` (10× `solve_clues` + `sample_secret`) | 14,496 B / 16,132 B | 0.125 | 0.125 | **0.083** | **1.51×** | Full 8-predicate unit |
| `send_more_money` (20× `send_more_money`) | 13,560 B | 0.029 | 0.029 | **0.016** | **1.76×** | Native choice enumeration |

### Addendum 2 (2026-11-10): Tracks 1–5 (`84812e8` — `queens`, Consumed Symbolic Terms, Unboxed `assertz`, Static Fact Hashing, & Default `length/2`)

4. **Whole-Search `queens/2` & Generalized Multi-Argument Head Exclusivity (`Clause.hs`, `Run.hs`)**:
   - Proves `selExclusive = True` across multiple arguments when earlier arguments have no repeated variables (`noatt/3`, `remove/3`, `absent/2`), admits integer-list units (`intOnlyData`) as `upRerunFree = True`, and runs `drainNativeFindAll` across all native clause units.
   - Fuses `wGetList` + `wUnifyVar` + `wUnifyVar` into a single `wGetListVarVar` WAM instruction and eliminates `Seq` round-trips in `findall` / `minimize`.
5. **Consumed Symbolic Terms (`derivrkeep` / `derivracc2`), Type-Guard Exclusivity, Functor Switch & Tail-Call Heap Reclamation (`Infer.hs`, `Compile.hs`, `Clause.hs`, `Jit.hs`)**:
   - Adds `typeGuardOption`, `GuardTag`, and `headVsTypeGuard`/`typeGuardPair` so `tsize/2` is proven `selExclusive = True`; adds `arg0FunSwitch` binary-search dispatch on leading compound functors (`d/3`, `tsize/2`); trims trail entries at neck cuts; reclaims heap/trail (`clauseCanReclaimTailH`) at tail calls after `once` (`derivrkeep`, `derivracc2`); and expands the native JIT heap buffer to 64M words (`512 MB` virtual, lazy page fault), eliminating `heap limit -> interpreter` bailouts completely.
6. **Unboxed Dynamic Fact Store (`DynFact` in `Run.hs`), Incremental Indexing & `pFact2` (`Program.hs`, `Compile.hs`, `Run.hs`), and Default `length/2` + `INFERA_MAX_DEPTH`**:
   - Stores 1-argument immediate dynamic facts in a flat mutable `IOUArray Int Word64` (`DynIntBuf`) and 2-argument immediate facts as unboxed words (`DFImm2`) with incremental `O(1)` first-argument indexing on `assertz`/`retract` and a direct `drainDynamicFindAll` loop; updates `predIndex` incrementally in `addClause` and adds an open-addressed unboxed `pFact2` (`lookupFact2`) table; provides a built-in fallback `length/2` and configurable `INFERA_MAX_DEPTH`.

#### Standard CLI Benchmark Suite (`bench/run.py --runs 5`, Apple M4 arm64)

| Benchmark | Workload | Infera (`84812e8`) | Scryer 0.10.0 | Speedup vs Scryer |
| :--- | :--- | ---: | ---: | ---: |
| `nrev` | Naive reverse 30-element list (3,000×) | **0.0423s** | 0.1595s | **3.77× faster** |
| `loop` | Tail-recursive countdown (90,000×) | **0.0289s** | 0.0645s | **2.23× faster** |
| `fib` | Untabled `fib(25)` (`<- notable.`) | **0.0297s** | 0.0857s | **2.89× faster** |
| `queens` | 8-Queens all solutions | **0.0292s** | 0.0639s | **2.19× faster** |
| `zebra` | Einstein's Zebra puzzle (300×) | **0.0903s** | 0.6052s | **6.70× faster** |
| `deriv` | Symbolic differentiation (30,000×) | **0.0309s** | 0.3435s | **11.12× faster** |
| `primes` | Trial-division primes up to 20,000 | **0.0742s** | 0.5978s | **8.06× faster** |

#### Full 13-Workload Competitor Comparison (`-O2`, untabled `<- notable.`)

Direct Apple M4 arm64 measurements for **Infera (`84812e8`)** (`JIT=1` and `JIT=0`) and **Scryer 0.10.0**, shown alongside the prior **Infera (`9a93cfe`)**, **SWI-Prolog 10.0.0**, **GNU Prolog 1.6.0** (consulted bytecode), and **Trealla v3.14.62** baselines from above:

| Workload | Infera (`84812e8` JIT) | Infera (`84812e8` No-JIT) | Prior Infera (`9a93cfe`) | Scryer 0.10.0 (M4) | SWI 10.0.0 (Nov 9) | gprolog 1.6.0 (Nov 9) | Trealla v3.14.62 (Nov 9) | Standing Now |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| `hello` (startup + halt) | **0.018s** | 0.019s | 0.004s | 0.048s | 0.009s | 0.007s | 0.024s | **2.6× faster** than Scryer |
| `nrev` (30 × 30k) | **0.136s** | 1.662s | 0.129s | 1.017s | 0.971s | 0.693s | 3.860s | **5.1×–7.5× faster** than gprolog / SWI / Scryer |
| `tak(24,16,8)` (untabled) | **0.028s** | 0.398s | 0.577s | 0.313s | 1.626s | 0.490s | 1.380s | **11×–58× faster** than Scryer / gprolog / SWI |
| `fib(27)` (untabled) | **0.029s** | 0.111s | 0.149s | 0.143s | 0.382s | 0.123s | 0.256s | **4.2×–13.2× faster** than gprolog / Scryer / SWI |
| `queens(9)` (all 352) | **0.531s** | 1.024s | 0.619s | 0.842s | 0.539s | 0.637s | 1.338s | **Parity with SWI**, **1.2×–1.6× faster** than gprolog / Scryer |
| `primes` (up to 20k) | **0.080s** | 0.619s | 0.087s | 0.658s | 0.489s | 0.481s | 1.342s | **6.0×–8.2× faster** than gprolog / SWI / Scryer |
| `zebra` (300×) | **0.090s** | 0.660s | 0.089s | 0.603s | 0.257s | 0.286s | 0.838s | **2.9×–6.7× faster** than SWI / gprolog / Scryer |
| `derivr` (30k×, discarded) | **0.040s** | 0.448s | 0.113s | 0.367s | 0.152s | 0.228s | 0.561s | **3.8×–9.2× faster** than SWI / gprolog / Scryer |
| `derivrkeep` (30k×, inspected) | **0.041s** | 0.454s | 0.263s | 0.371s | 0.150s | 0.240s | — | Flipped `1.76×` loss vs SWI into **3.7× faster** |
| `derivracc2` (30k× + `tsize/2`) | **0.104s** | 2.330s | 3.753s | 1.806s | 1.241s | 1.568s | — | **35.9× speedup**; now **11.9×–17.3× faster** than SWI / Scryer |
| `assertz` (100k + `findall` + sum) | **0.056s** | 0.077s | 0.139s | 0.397s | **0.050s** | 0.064s | 0.146s | Beats gprolog, Trealla & Scryer (**7.1×**); within **~10% of SWI** |
| `findall` (50k solutions) | **0.019s** | 0.044s | 0.040s | 0.071s | 0.020s | 0.021s | 0.054s | **Parity / slight edge** over SWI & gprolog; **3.8× faster** than Scryer |
| `index` (2k facts × 20 rounds) | 0.047s | 0.048s | 0.039s | 0.087s | **0.028s** | 0.035s | 0.052s | Beats Scryer (**1.8×**) & Trealla; ~19ms behind SWI due to parser load time |
| `deep_200k` (`INFERA_MAX_DEPTH=1000000`) | **0.019s** | 0.119s | — (depth error) | — | — | — | — | Configurable `INFERA_MAX_DEPTH` + native `deep_sum/2` (6.3× JIT speedup) |

#### Summary of Ranking Shifts After `84812e8`

- **Consumed symbolic terms (`derivrkeep`, `derivracc2`)**: Previously Infera's steepest loss (`1.76×` and `3.03×` slower than SWI because `once` and tail calls leaked native heap and fell back to the bytecode interpreter). With native `tsize/2` exclusivity, `arg0FunSwitch`, `clauseCanReclaimTailH`, and the 64M-cell JIT heap, `derivracc2` improved **35.9×** (`3.753s` → `0.104s`), making Infera **~12× faster than SWI** and **~17× faster than Scryer**.
- **Untabled recursion (`tak`, `fib`)**: Previously slower than GNU Prolog (`0.577s` and `0.149s`) due to hitting the old 4M-cell JIT heap limit. Now stays 100% native (`0.028s` and `0.029s`), beating GNU Prolog by **17×** and **4.2×** even with tabling disabled.
- **Backtracking & `findall` (`queens`, `findall 50k`)**: Fusing `wGetListVarVar` and removing `Seq` conversions cut `findall (50k)` in half (`0.040s` → `0.019s`, matching SWI's `0.020s`) and brought `queens(9)` to `0.531s` (matching SWI's `0.539s` and beating GNU Prolog's `0.637s` and Scryer's `0.842s`).
- **Dynamic database (`assertz 100k`)**: Incremental `O(1)` first-argument indexing on `assertz`/`retract` plus `DynIntBuf` cut `assertz` from `0.139s` to `0.056s`, overtaking GNU Prolog (`0.064s`), Trealla (`0.146s`), and Scryer (`0.397s`), and sitting within ~10% of SWI (`0.050s`).
- **Remaining gaps**:
  1. Source-file parsing overhead on multi-thousand-clause files (`index` with 2,000 static clauses takes `0.047s` total, of which `< 2 ms` is the 40,000 hash lookups).
  2. Issue #7 (`plus`/`minus` ground arithmetic functor evaluation when used as unquoted data constructors).
