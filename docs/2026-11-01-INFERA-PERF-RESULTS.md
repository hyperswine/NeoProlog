# Infera performance results and fixes (2026-11-01, report)

Measured on one shared, noisy Linux x86-64 VM (8 vCPU, Debian 13, glibc 2.41). Times may vary by about ±5–10 %. Jack's macOS arm64 machine was **not** measured; macOS arm64 is exercised only by CI (`macos-26`). No release has been cut: these changes are on `main` after v2.2.0. Shipping them through Homebrew needs a new tag, release tarballs and a tap bump.

## Methodology

- Each sample is a fresh process, timed by wall clock, so startup, load and printing are included. Cells show the **median of 3** runs in seconds, then the ratio to swipl's median. Runs were interleaved across systems.
- Every program prints its answer. The answers were checked to agree across all systems before any time was compared.
- **Infera:**
  - v2.2.0 is tag `cace1e3`, built from source with GHC 9.8.2 at `-O2`, the same flags as CI. The official linux-x86_64 tarball needs glibc ≥ 2.42 and does not start on Debian 13.
  - "main" is the tree after PRs #5, #6, #8 and #9.
  - "Default" means programs as written, with automatic tabling on.
  - JIT off means `INFERA_JIT=0`.
- **Competitors:**
  - SWI-Prolog 10.0.0 (conda-forge)
  - GNU Prolog 1.6.0 (built from git; consulted bytecode rather than native `gplc`; stacks raised)
  - Trealla (git 4e76)
  - Scryer Prolog 0.10.0 (cargo)
- **Programs:** one plain translation per system; no cuts, same algorithms. nrev, queens and fib come from `bench/bench.pl`.
  - nrev30 ×30000
  - tak(24,16,8)
  - 9-queens, all solutions (perm+safe)
  - fib(27)
  - list sieve primes to 20000
  - assertz: assert 100k facts, then findall and an accumulator sum
  - derivr: classic deriv, 4 expressions ×30000, with constructors named `add`/`sub` (see issue #7)
  - zebra ×300
  - hello (startup)
- The scripts, programs and raw samples are kept outside the repo, in the benchmark workspace (`run.py`, `progs/`, `raw*.jsonl`).

## Comparison (linux-x86_64, noisy VM; seconds, median of 3, ×swipl)

| program | Infera 2.2.0 (default) | Infera main (default, JIT on) | Infera main (JIT off) | swipl 10.0.0 | gprolog 1.6.0 | trealla | scryer 0.10.0 | answers |
|---|---|---|---|---|---|---|---|---|
| hello | 0.006 | 0.005 | 0.004 | 0.009 | 0.007 | 0.025 | 0.073 | hello |
| nrev | >60 s (timeout) | 0.406 (0.39×) | 2.569 (2.47×) | 1.039 (1.00×) | 0.681 (0.66×) | 3.887 (3.74×) | 1.231 (1.18×) | 30 |
| tak | 0.050 (0.03×) | 0.017 (0.01×) | 0.018 (0.01×) | 1.521 (1.00×) | 0.465 (0.31×) | 1.258 (0.83×) | 0.548 (0.36×) | 9 |
| queens | 0.606 (1.12×) | 0.599 (1.10×) | 1.383 (2.55×) | 0.543 (1.00×) | 0.628 (1.16×) | 1.243 (2.29×) | 0.929 (1.71×) | 352 |
| fib | 0.007 (0.02×) | 0.007 (0.02×) | 0.006 (0.02×) | 0.362 (1.00×) | 0.113 (0.31×) | 0.226 (0.63×) | 0.183 (0.50×) | 196418 |
| primes | 0.985 (3.56×) | 1.003 (3.63×) | 1.006 (3.64×) | 0.276 (1.00×) | 0.482 (1.75×) | 1.020 (3.69×) | 0.649 (2.35×) | 2262 |
| assertz | – | 0.151 (3.06×) | 0.150 (3.03×) | 0.049 (1.00×) | 0.065 (1.31×) | 0.143 (2.88×) | 0.583 (11.78×) | 5000050000 |
| derivr | – | 3.029 (2.85×) | 3.072 (2.89×) | 1.063 (1.00×) | 1.187 (1.12×) | 3.569 (3.36×) | 1.601 (1.51×) | 407 |
| zebra | 3.894 (7.09×) | 1.984 (3.61×) | 2.095 (3.81×) | 0.550 (1.00×) | 0.614 (1.12×) | 1.780 (3.24×) | 1.450 (2.64×) | japanese |

For Infera 2.2.0 default, assertz and derivr also timed out (more than 60 s) in a separate run with the same programs. On v2.2.0, the assert slowdown and the auto-tabled counter loop are the causes.

fib and tak under Infera's default are **memoised by tabling**. They measure tabling, not raw execution speed, so they are not comparable with the other systems. With `<- notable.`, Infera 2.2.0 measured fib 0.12 s (0.35× swipl) and tak 0.58 s (0.38×).

**Reading:** Infera main is now:
- **fastest of all on nrev:** the JIT has a native routine for this exact shape; with the JIT off it is 2.5×
- **level with swipl and gprolog on queens**
- about **3–3.8× slower than swipl on primes, assertz, deriv and zebra**: general unification and structure work, roughly Trealla's level
- **fastest at startup** (about 5 ms)

## Repo claims vs measured

- `docs/2026-10-15-PERFORMANCE.md` / `docs/2026-10-30-JIT-ACTIVATION.md` report loaded-query milliseconds inside the `core-major` harness. Startup is excluded, the batches are small, and they ran on the author's machine (platform not stated). They claim core-nrev 0.93× SWI, core-fib 3.0×, core-queens 1.4× and core-loop 0.03×.
- Here, whole-process on x86-64: nrev 0.39×, queens 1.1×, fib 0.35× untabled.
- The repo harness has no tak, primes, zebra, deriv or assert cases, and runs everything with `<- notable.`. That is where the problems below were hidden.

## Problems found and what changed

| # | Problem | Root cause | Status | Fix / PR | Before → after |
|---|---|---|---|---|---|
| 1 | With the JIT on, a countdown loop to 100,000 reported "Search depth limit reached"; with it off, `true.` | **Verified.** The interpreter's limit is continuation depth (`contDepth`), which last calls don't increase. JIT routines ticked the budget per iteration (nrev: 1+2+…+L). | merged | #5: tail iterations don't tick, nrev ticks once per nested call, declines without headroom; `test/jit_depth.py` | `loop 100000`…`1000000`: limit → `true.`; JIT on/off agree on 18 queries, including a sweep across the limit |
| 2 | assert O(n²) | **Verified.** `Map.insertWith (flip (++))` built a lazy left-nested `old ++ [new]` chain, forced at O(n) per element on first read | merged | #6: facts in `Data.Sequence`; `test/assert_scaling.py` | 10k: 0.89 s → 0.03 s; 100k: 205 s → 0.18 s; 1M: 1.6 s |
| 3a | Full table-map scan per tabled answer | **Verified** (profile: 31.5M `teComplete` calls at K=3000) | merged | #8: append-only completed-table log | tak (default) 0.06 s → 0.02 s |
| 3b | Default auto-tabling made counter loops quadratic and doubled zebra | **Verified** (profile). The tabled tail call keeps a fixpoint frame per level; machine `collect` is 79 % at K=10k. The second fixpoint pass re-runs the body (2× calls). | merged, **default behaviour change** | #9: deterministic counter-driven loops are not auto-tabled (criterion in `docs/2026-11-01-AUTO-TABLING-COST.md`); `perf-tabled-counter-loop` check hint; `test/autotable.py` | nrev ×30000: >60 s → 0.41 s; zebra 3.9 s → 2.0 s; fib/tak still memoised; 23 examples byte-identical with JIT on/off |
| 4 | User terms `plus`/`minus`/`mul`/`div`/`mod`/`neg`/`abs`/`min`/`max` are evaluated as arithmetic (deriv 405 vs 407 elsewhere) | **Verified.** Operators parse to those names; ground call arguments are evaluated (`compileArg'`/`PArith`, `normArithTerm`), and so is answer printing (`deepEval`) | **open: issue #7** (design decision; no behaviour change) | – | – |

## Merge record

- #5 → `f09a2ef`
- #6 → `814c1c9`
- #8 → `3487a6c`
- #9 → `718f63e`

All are plain merge commits. Each PR's CI was green on ubuntu-latest and macos-26 immediately before its merge.

## Open

- Issue #7 (arithmetic functors as data): a design decision for Jack.
- The `Infera.Engine.Reference` and `Infera.Machine.Builtins` assert paths still use the `flip (++)` pattern. The default CLI path doesn't use them.
- The linux-x86_64 release binary requires glibc ≥ 2.42.
- macOS arm64 has been tested only by CI. No local arm64 benchmark exists.
- No release tag yet. A Homebrew upgrade needs a new tag, release assets and a tap bump.
- Infera is still about 3× behind SWI on general unification-heavy programs (primes, zebra, deriv, assertz).
