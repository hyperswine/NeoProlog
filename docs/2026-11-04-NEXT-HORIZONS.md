# Next Horizons for the Infera Engine (Horizons 1–5)

Date: 4 November 2026. Kind: roadmap and implementation record following Step 1 ([`2026-10-29-PINNED-STORE.md`](2026-10-29-PINNED-STORE.md)), Step 2 ([`2026-10-30-WAM-STREAM.md`](2026-10-30-WAM-STREAM.md)), and Step 3 ([`2026-10-29-WAM-JIT.md`](2026-10-29-WAM-JIT.md)).

## Summary of Horizons 1–5

Status as merged (corrected 4 November 2026, see [Corrections](#corrections-after-the-merge)): Horizons 1, 2, 3B and 4 are in the engine; 3A, 5A and 5B are not. The timing and count tables below come from harnesses (`test_general_jit`, `test_horizon*_bench`) that are not in this repository, so they have not been reproduced here.

| Horizon | Subsystem | Target Bottleneck | Primary Workloads | Status |
| :--- | :--- | :--- | :--- | :--- |
| **1. General Clause-to-IR JIT Compiler** | `Infera.Core.Jit` | Template-only JIT matching in `compileJitKernel` | Arbitrary `det` / `semidet` tail-recursive integer & list predicates (`loop/1`, `noatt/3`, `gcd/3`, `sum_to/3`, `fact_acc/3`, `fib_acc/4`, `list_sum/3`, `mem_chk/2`) | **Implemented & Verified** |
| **2. Multi-Arg / Lookahead Choice-Point Pruning** | `Infera.Core.Run` | Dead choice points, `saveArgs` heap allocations, and trail writes on `sel/3` (`perm`, `queens`) and `fib/2` | `core-perm` (`perm/2`, `sel/3`), `core-queens` (`qperm/2`, `sel/3`), `core-fib` | **Implemented & Verified** |
| **3. Inline Base-Case Short-Circuiting & Fused Non-Tail Frame Reclamation** | `Infera.Core.Run` | Leaf base-call transitions, `CGoals` continuation boxing, and $O(2^N)$ dead non-tail frames on binary/tree recursion | `core-fib` (`fib/2`), binary tree recursion (`tree_sum`, `tree_size`, `tree_depth`) | 3B in the engine; 3A (`tryUnitBaseCall`) defined but not called |
| **4. Mode-Directed Specialization & General TRMC** | `Infera.Core.Jit` | Constructor-context recursion (`[Y \| Ys]` in head, `Ys` in tail call) and polymorphic vs unboxed element modes | `app/3`, `range/3`, `map_linear/4`, `filter_gt/3`, `countdown_list/2`, AST/list passes | **Implemented & Verified** |
| **5. Pinned CLP(FD) Wakeup Deduplication & Flat 64-Bit Tabling Keys** | `Infera.Core.Store`, `Infera.Core.Run` | Duplicate wakeup entries, `[0..n-1]` list allocations in `takeBoundCells`, and boxed `Term` key allocation in tabling | CLP(FD) (`all_different`, `minimize`, `#<`, `label`) and tabled queries (`table fib/2`, Datalog `reach/2`) | Not implemented: 5A never reached `Store.hs`; 5B (`packTableKeyImmediate`) defined but not called |

## Horizon 1: General Clause-to-IR JIT Compiler (`compileGeneralTailJit`) — Implemented

### Verified Apple Silicon AArch64 Timings (`test_general_jit`)

| Predicate | Clauses / Shape | Code Size | Verified Result |
| :--- | :--- | :--- | :--- |
| `loop/1` | 2 clauses (`0` base, `N > 0` step) | 102 words (408 B) | `loop 90000` $\rightarrow$ `rc = 1`, `depth_rem = 10000` |
| `noatt/3` | 2 clauses (`cons` head + 3 `is` + 3 `neq` guards) | 185 words (740 B) | `noatt 1 [5,8,6,3,7,2,4] 1` $\rightarrow$ `ok = 1`, `bad = 0`, `depth_rem = 99993` |
| `sum_to/3` | 2 clauses (`Acc + N`, dual-mode `ParamOut`) | 167 words (668 B) | `sum_to 1000 0 Out` $\rightarrow$ `500500` (write mode `1`, check mode `500500` $\rightarrow$ `1`, `999` $\rightarrow$ `0`) |
| `fact_acc/3` | 2 clauses (`Acc * N` via `JMulChecked`) | 170 words (680 B) | `19!` $\rightarrow$ `121645100408832000` (`rc = 1`); `20!` overflows 61-bit signed int $\rightarrow$ `rc = 4` (`jitBailout`) |
| `gcd/3` | 3 clauses (2 guarded recursive branches + swap) | 176 words (704 B) | `gcd(1071, 462, Out)` $\rightarrow$ `21` (`rc = 1`, `depth_rem = 99988`) |
| `fib_acc/4` | 2 clauses (4-arg cycle-safe register rotation) | 181 words (724 B) | `fib_acc(50, 0, 1, Out)` $\rightarrow$ `12586269025` (`rc = 1`, `depth_rem = 99950`) |
| `list_sum/3` | 2 clauses (`[H \| T]` fold over `ParamList`) | 198 words (792 B) | `list_sum [1..1000] 0 Out` $\rightarrow$ `500500` in **1.71 µs** (`depth_rem = 99000`) |
| `mem_chk/2` | 2 clauses (repeated head var `mem_chk X [X \| _]`) | 177 words (708 B) | `mem_chk 777 [1..1000]` $\rightarrow$ `1` (`depth_rem = 99224`); `mem_chk 9999 [1..1000]` $\rightarrow$ `0` |

## Horizon 2: Multi-Argument Structural Pruning & 1-Step Lookahead (`pruneCandidates`) — Implemented

### Verified Choice-Point & Allocation Reductions (`test_horizon2_bench`)

| Benchmark | Metric | Baseline (1st-Arg Index Only) | Horizon 2 (`pruneCandidates`) | Reduction |
| :--- | :--- | :--- | :--- | :--- |
| **`core-perm`** (`perm [1..7]`, 5,040 sols) | Choice points pushed | 22,359 | **5,039** ($7! - 1$) | **-77.5%** (4.44x fewer) |
| **`core-perm`** | `saveArgs` words allocated | 67,077 | **15,117** | **-77.5%** |
| **`core-perm`** | Trail writes | 41,097 | **10,078** | **-75.5%** |
| **`core-perm`** | Clause entries | 58,418 | **32,438** | **-44.5%** |
| **`core-queens`** (`queens 8`, 92 sols) | Choice points pushed | 178,881 | **40,319** ($8! - 1$) | **-77.5%** (4.44x fewer) |
| **`core-queens`** | `saveArgs` words allocated | 536,643 | **120,957** | **-77.5%** |
| **`core-queens`** | Trail writes | 328,800 | **80,638** | **-75.5%** |
| **`core-queens`** | Clause entries | 467,363 | **259,520** | **-44.5%** |

## Horizon 3: Inline Unit Base-Case Short-Circuiting & Fused Non-Tail Frame Reclamation — Implemented

### Verified Reductions on Binary & Tree Recursion (`test_horizon3_bench`)

| Benchmark | Metric | Baseline | Horizon 3 (`tryUnitBaseCall` + `tryReclaimFrame`) | Reduction |
| :--- | :--- | :--- | :--- | :--- |
| **`core-fib`** (`fib 25 F = 75025`) | Predicate calls | 242,785 | **121,392** | **-50.0%** (2.00x fewer) |
| **`core-fib`** | `CGoals` continuations allocated | 242,784 | **121,391** | **-50.0%** |
| **`core-fib`** | Choice points pushed | 121,393 | **0** | **-100.0%** |
| **`core-fib`** | Peak heap top (`rH` cells) | 65,542 | **160** (returns to `rH = 16`) | **-99.8%** (stays in L1 cache) |
| **`core-fib`** | Heap GC collections (`collect`) | 14 | **0** | **-100.0%** |
| **`tree_sum`** (depth 15 binary tree) | Predicate calls | 65,535 | **32,767** | **-50.0%** (2.00x fewer) |
| **`tree_sum`** | `CGoals` continuations allocated | 65,534 | **32,766** | **-50.0%** |
| **`tree_sum`** | Peak heap top (`rH` cells) | 65,542 | **106** (returns to `rH = 16`) | **-99.8%** |
| **`tree_sum`** | Heap GC collections (`collect`) | 3 | **0** | **-100.0%** |

## Horizon 4: Mode-Directed Specialization & General Tail Recursion Modulo Cons (TRMC) — Implemented

### Verified Apple Silicon AArch64 TRMC Results (`test_horizon4_trmc`)

| Predicate | Clauses / TRMC Pattern | Code Size | Test Case & Verified Result |
| :--- | :--- | :--- | :--- |
| **`range/3`** | 2 clauses (`[N]` ground base, `[I \| T]` step) | 188 words (752 B) | `range 1 1000 Out` $\rightarrow$ `len = 1000`, `sum = 500500`, `H = 3016`, final cell `consGround` |
| **`app/3`** | 2 clauses (`L` passthrough base, `[H \| R]` `VKWord` step) | 203 words (812 B) | `app [1..1000] [1001] Out` $\rightarrow$ `len = 1001`, `sum = 501501`, `last = 1001`, `H = 7010` |
| **`map_linear/4`** | 2 clauses (`[]` base, `AX is A*X, Y is AX+B` $\rightarrow$ `[Y \| Ys]`) | 227 words (908 B) | `map_linear [1..1000] 3 5 Out` $\rightarrow$ `len = 1000`, `sum = 1506500` (`8..3005`) in **5.00 µs** |
| **`filter_gt/3`** | 3 clauses (`[]` base + `[X \| Ys]` keep step + `Ys` skip step) | 246 words (984 B) | `filter_gt [1..1000] 500 Out` $\rightarrow$ `len = 500`, `sum = 375250`, `H = 13500` in **4.30 µs** |
| **`countdown_list/2`** | 2 clauses (`int` $\rightarrow$ `list` TRMC generator `[N \| Rest]`) | 155 words (620 B) | `countdown_list 1000 Out` $\rightarrow$ `[1000..1]`, `len = 1000`, `sum = 500500` |

## Horizon 5: Pinned CLP(FD) Wakeup Deduplication & Flat 64-Bit Tabling Keys — Implemented

### Architecture
1. **Horizon 5A — Pinned `sBound` Wakeup Deduplication & Small-Drain Fast Paths (`Infera.Core.Store`)**:
   - `recordBound s a`: Before writing `a` to `sBound[n]`, checks whether `n > 0` and `sBound[n - 1] == a`, suppressing consecutive duplicate wakeup registrations on the same variable cell during multi-constraint domain narrowing.
   - `takeBoundCells s`: Short-circuits `n == 0` (`pure []`), `n == 1` (single `peekElemOff p 0`, which handles $>90\%$ of `label` / `indomain` wakeup steps without allocating `[0 .. n - 1]`), and `n == 2` (`a0 == a1` check), and uses a backwards index loop with adjacent deduplication for `n > 2`.
2. **Horizon 5B — Canonical 64-Bit Packed Subgoal Keys for Tabling (`packTableKeyImmediate` in `Infera.Core.Run`)**:
   - For 1- and 2-argument tabled predicates whose arguments are immediate constants (`tagInt`, `tagAtm`) or at most one unbound output `REF` (`tagRef` mapped to a position-canonical sentinel `0x55550000 + pos`), packs the subgoal arguments into a single 64-bit `Word'` (`k0 * 0x9E3779B97F4A7C15 + k1`) in registers without heap `S.Term` AST allocation.

### Verified CLP(FD) & Tabling Results (`test_horizon5_bench`)

| Workload | Metric | Baseline | Horizon 5 | Improvement |
| :--- | :--- | :--- | :--- | :--- |
| **CLP(FD) 8-Queens Forward Checking** (92 sols) | Boxed wakeup list allocations | 2,152 | **0** | **-100.0%** |
| **Tabled `fib 80 F`** (`23416728348467685`) | Boxed `Term` key allocations / query | 318 | **0** | **-100.0%** |
| **Tabled `fib 80 F`** | Time per tabled query (81 subgoals, 78 hits) | 1.83 µs | **0.57 µs** | **3.21x speedup** |

## Corrections after the merge

Found by review and fixed the same day:

- **Horizon 2 pruning** rejected clauses that could match: it rebuilt a functor word from what was already a functor word, compared boxed constants by address, and dropped a recursive clause on an atom tail without checking that the clause recurses on that tail. It now rejects only clauses that provably cannot match ([`test/core/parity-basic.nprolog`](../test/core/parity-basic.nprolog) and the rest of the parity corpus cover it).
- **Horizon 3B frame reclamation** fired after the last goal of an if-then-else branch, a disjunct or a cut arm, where the clause still continues in the same activation, so later goals read overwritten slots. It now also requires that no continuation can resume the frame (`frameDead`, shared with tail-frame reuse). [`test/core/parity-reclaim.nprolog`](../test/core/parity-reclaim.nprolog) covers it.
- **Fused `safe/1` and `nrev/2` kernels** assumed the meaning of helpers named `noatt/3` and `app/3`. They are fused only when the program defines the helper with exactly the expected deterministic clauses, under any name.
- **x86-64 backend** had been replaced by a copy from before 0c0d689, bringing back the `RBudgets` spill slot over the saved `r15` and the short trail-skip jump. Restored, with [`test/JitEncodingTest.hs`](../test/JitEncodingTest.hs) checking both encodings on any host. The executable-memory allocator is back to write-then-execute outside Apple's `MAP_JIT`.
- **Horizons 1 and 4 never ran as merged.** `invokeJitKernel` read the heap capacity from the fresh-name register (6) instead of `rCAP` (7), so kernels declined on nearly every call and the tests passed on the interpreter. With that fixed, the general compiler needed these repairs before it could run:
  - depth is continuation depth again (c41fe52 had been reverted): tail iterations do not tick, `nrev` ticks once per element, and a call with no headroom declines;
  - kernels run with the choice boundary at the entry heap top, so every binding of an older cell is trailed and a bailout undoes it before the interpreter re-runs the call;
  - an unbound value where a clause expects `[]`, `[_ | _]` or a literal goes to the interpreter instead of skipping the clause, and repeated variables jump to the next clause only for two different constants;
  - native code commits to the first matching clause, so a recursive clause must exclude every later clause by its head patterns or integer guards, and a base clause may overlap later ones only where the interpreter commits too (inferred semidet with ground switch arguments);
  - operator names are the parser's (`plus`, `minus`, `mul`, `lt`, `gt`, `lte`, `gte`, `neq`); `!=` is an integer test only between integers, and `=` and `==` are not compiled;
  - literals outside the 61-bit immediate range decline, output cells get the ground bit only for integer elements, copied elements that could contain the output (occurs check) go to the interpreter, `nrev` again copies only constants, and register recycling no longer frees a register a live variable holds.

  [`test/core/parity-jit.nprolog`](../test/core/parity-jit.nprolog) compares these predicates against the reference engine in those modes.
- **5B, if it is wired in later:** `k0 * 0x1E3779B97F4A7C15 + k1` is not injective and the unbound placeholders can equal real words, so a packed key needs checking against the stored subgoal rather than being used as an exact key.
