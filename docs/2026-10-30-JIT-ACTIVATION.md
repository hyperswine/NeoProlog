# Making the native JIT reachable - 2026-10-30 (report)

Step 3 of [WAM-JIT](2026-10-29-WAM-JIT.md) was implemented and its kernels
were measured, but no compiled kernel could run. Three separate defects
stopped entry, and repairing them turned the JIT from inert into the
largest single win in the record: 9.9x on reverse, 141x on the counting
loop, 2.4x on 8-queens against the last release.

## What was broken

1. **Four matchers compared surface operators.** The AST stores internal
   names ([Syntax.hs](../src/Infera/Syntax.hs)), so `Compound ">"`,
   `"<"`, `"-"` and `"+"` never match `gt`, `lt`, `minus` and `plus`.
   `matchCountdownLoop`, `matchRangeLoop` and `matchNoattLoop` could not
   fire, and `matchSafeLoop` depends on `matchNoattLoop`. Only
   `matchAppendLoop` and `matchNrevLoop`, which match structure alone,
   compiled.
2. **Invocation read capacity from the wrong register.**
   `invokeJitKernel` took `rCAP` from register 6, which is `rFRESH`
   after [WAM-STREAM](2026-10-30-WAM-STREAM.md) left slot 4 unused, so
   it compared the heap top against the fresh-variable counter and
   declined every call. `rCAP` and `rTRAILCAP` are now exported and read
   by name.
3. **The store's trailing boundary is not the span's.** Native code
   trailed bindings of cells below `rHB`, the heap mark of the last
   choice point, while a mid-span bailout rewinds the heap to the JIT
   entry top, which is later. A binding of a cell allocated between
   those two marks was therefore neither trailed nor reset, and the
   interpreter that re-ran the call saw a binding to freed cells. The
   kernel is now given `entryH` as its boundary: everything the span can
   bind below it is trailed, and everything at or above it is discarded
   by the rewind.

Two further defects were found once kernels ran: a native loop bound an
output variable to a structure that contained it, which the interpreter
rejects by occurs check (`app [X] [] X`), and 8-queens' `safe/1` inherits
it. Both append and reverse now copy atomic elements only and return to
the interpreter for a compound or unbound element, and the check uses a
register the reverse kernel does not need for its depth step.

## Measurements

Same host, GHC 9.8.2, library and benchmark at `-O2`, `core-major --case C
--batch 20 +RTS -T -RTS`. Each column is three interleaved samples of the
whole process; the median of the three is the figure. `main` is
`74c1740` built from a worktree at the same profile, so all three columns
differ only in source. Every record reports `status: ok`,
`oracle_checked`, `independent_checked` and `fully_drained`.

| Case | `main` ms | JIT off ms | JIT on ms | vs `main` | JIT gain |
| --- | ---: | ---: | ---: | ---: | ---: |
| core-nrev | 8.577 | 6.893 | 0.867 | -89.9% (9.9x) | -87.4% |
| core-loop | 8.965 | 8.144 | 0.064 | -99.3% (141.1x) | -99.2% |
| core-fib | 38.481 | 31.813 | 31.836 | -17.3% (1.2x) | +0.1% |
| core-queens | 8.596 | 7.240 | 3.514 | -59.1% (2.4x) | -51.5% |

Allocation per query falls with the same changes, because the native span
allocates nothing for the counting loop and nothing that survives the call
for the others:

| Case | `main` MB | JIT off MB | JIT on MB |
| --- | ---: | ---: | ---: |
| core-nrev | 19.39 | 17.05 | 10.76 |
| core-loop | 12.97 | 20.81 | 8.57 |
| core-fib | 67.81 | 82.30 | 82.30 |
| core-queens | 20.29 | 21.65 | 15.16 |

The `JIT off` column isolates the interpreter work that landed since
`main`: `core-fib` and `core-queens` are 17% and 16% below it, `core-nrev`
21% below, and `core-loop` 9% faster with 8 MB more allocation, the
allocation regression [WAM-STREAM](2026-10-30-WAM-STREAM.md) records as an
open problem. `core-fib` has no kernel and so shows the interpreter gain
alone.

Raw records: [jsonl](../data/jsonl/engine-jit-activation-2026-10-30.jsonl)
(`source_fingerprint` `0dd7e1be…` for both current columns, `41aae485…`
for `main`) and the [TSV summary](../data/tsv/engine-jit-activation-2026-10-30.tsv).

## Scope

These are per-query CPU seconds for a loaded program, including Core
compilation of the query, execution, projection and validation. Source
loading, the Reference oracle and the Core preflight are excluded, as in
the earlier reports. The machine is shared; the three columns were
interleaved sample by sample, and the `JIT on` and `JIT off` columns come
from one binary differing only in `INFERA_JIT`.

`core-fib` is unchanged by construction: `fib/2` has two recursive calls,
two base clauses and arithmetic in the head, which is outside the
fragment. `range/3`, `perm/2`, `sel/3` and `queens/2` still decline on
inference (`Nondet`, correct for overlapping clauses), so the JIT reaches
only the deterministic spine of a workload.

## What the numbers do and do not say

The 141x on the counting loop is a native loop against a whole interpreted
query, but both columns now come from the same driver, same workload,
same validation, so it is a like-for-like measurement of what a user sees.
It is not a claim about the *ratio of native to interpreted execution* of
one call: the loop's cost per iteration in the interpreter includes the
goal dispatch, head match and call path the kernel also removes.

What it does say is that the JIT is worth enabling by default on
`aarch64-darwin`, which it now is (`INFERA_JIT=0` disables it), and that
the remaining fragment is the limit: `fib`, `range`, `perm`, `sel` and
`queens` still take the interpreter path entirely.

## Acceptance

`infera-test` passes in full with the JIT enabled: 497 checks, including
the forced-collection groups and every `parity_test/core` fixture. Each
parity fixture also produces byte-identical output with `INFERA_JIT=1`
and `INFERA_JIT=0` under the CLI.

The tests that caught the defects above, all already in the gate:

* `parity-structures` (`app [X] [] Y`, `app A B [1, 2, 3]`) caught the
  occurs-check binding.
* `CoreSlotsTest` `generated_reverse`, over lists of mixed integers and
  variables, caught the trailing-boundary defect.
* `core-major --case core-nrev` and `--case core-loop` with
  `INFERA_JIT_DEBUG=1` report `compiled` for `app/3`, `nrev/2`, `loop/1`,
  `safe/1` and `noatt/3`, and no `entry declined` line.

## Call path, later the same day

Two follow-ups: the price of entering native code, and the allocation the
tree path reports it pays.

### Entering a kernel

`invokeJitKernel` cost about 25 ns for a kernel that does almost nothing
(`loop/1` with argument 1, measured directly against the compiled kernel).
Of that, 8 ns was poking the state block, 2 ns reading it back and 3-5 ns
the indirect call. Three changes halve it to **15 ns**:

* The result was `IO (Maybe (Int64, Int))`, allocating a `Just`, a tuple
  and two boxed scalars on every call, and the depth component was never
  read by either caller. It is now the kernel's own return code, `IO Int64`,
  so nothing is allocated on the way out.
* `withForeignPtr` guarded a block the kernel already holds; the address is
  taken once at install and kept beside the `ForeignPtr` that keeps it
  alive.
* `budgetAllocIdx` was written on every call and read by no kernel.

The gain is only visible when calls are cheap. Five million one-element
`app/3` calls in an interpreted loop take 1.78 s interpreted and 1.67 s
through the kernel, up from 1.71 s: the native call was already at parity
with interpretation for that shape, and now it is 4% ahead instead of level.

### Allocation

The tree path's own report blamed the presence of the stream interpreter.
That does not reproduce. `INFERA_CORE_STREAM=0`, deleting the stream
dispatch from `enterClause`, deleting the JIT dispatch from `callPlain`,
rebuilding `callPlain` in its pre-JIT shape, and reverting the `bindQuick`
fast path all leave `core-loop`'s per-query allocation at 20.81 MB to four
digits. What did reproduce is a plain per-call cost: `loop 1000` against
`loop 101000` gives 48 bytes per iteration on `74c1740` and 136 bytes now,
with a per-process fixed cost of 9.87 MB against 9.88 MB.

Ruled out by measurement, each with its own build:

| Suspect | Experiment | Result |
| --- | --- | --- |
| stream dispatch | branch deleted from `enterClause` | 23.62 MB, unchanged |
| JIT dispatch | branch deleted from `callPlain` | unchanged |
| `callPlain`'s shape | rebuilt as it was before the JIT | 136 B/iteration |
| `bindQuick` fast path | reverted to `numericTarget`+`unify` | unchanged |
| the pinned store | 200,000 frame alloc/reset/read/write | 8.507 vs 8.509 MB |
| per-query compilation | fixed cost of the same CLI run | 9.87 vs 9.88 MB |
| `Cont`'s new constructor | dummy constructor added to `74c1740` | 48 B/iteration, unchanged |

So the cost is one allocation of about eleven words per call, in code the
two revisions share textually, and it is not the branch, the result type,
the frame arithmetic or the continuation type. The next instrument is a
cost-centre profiling build, which this tree cannot produce without
profiled dependencies.

One allocation was found and removed on the way: `pruneCandidates` built
the kept-clause list for every call whose first argument was an integer,
including the common case where no clause is rejected. Deciding that case
without allocating took `core-nrev` from 17.05 MB to 16.42 MB per query.

### Final position against `74c1740`

Same protocol as above, five interleaved samples per column, medians:

| Case | `main` ms | JIT off ms | JIT on ms | CPU | Allocation |
| --- | ---: | ---: | ---: | ---: | ---: |
| core-nrev | 8.537 | 6.876 | 0.827 | -90.3% | 19.39 -> 10.11 MB (-47.8%) |
| core-loop | 8.948 | 8.093 | 0.053 | -99.4% | 12.97 -> 8.57 MB (-33.9%) |
| core-fib | 38.399 | 31.792 | 31.932 | -16.8% | 67.81 -> 82.30 MB (+21.4%) |
| core-queens | 8.603 | 7.192 | 3.443 | -60.0% | 20.29 -> 14.77 MB (-27.2%) |

Raw records: [jsonl](../data/jsonl/engine-call-path-2026-10-30.jsonl),
[TSV](../data/tsv/engine-call-path-2026-10-30.tsv). `infera-test` passes
(497 checks) with the JIT enabled, and every `parity_test/core` fixture is
byte-identical with `INFERA_JIT=1` and `INFERA_JIT=0`.

Three of four workloads now allocate less than the last release and all
four are faster. `core-fib` is the exception in both columns that matter:
it has no kernel, so it carries the interpreter's per-call allocation
with none of the compensation.

## Remaining work

1. **The per-call allocation above**, found but not localized.
2. **Fragment growth**, in the plan's order: structures as arguments,
   multi-clause selection as a jump table, single-goal builtins, then
   control constructs.
