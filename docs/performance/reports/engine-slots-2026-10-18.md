# Core profiling, reusable slots and tail frames - 2026-10-18

Reusable activation operands and in-place tail frames are implemented and pass
the correctness suite. They establish substantial actual frame reuse, but this
iteration is not a general throughput improvement: the checked loop is 4.3%
faster, reverse is 12.1% slower, and GHC allocation rises on both. The change
does not close the gap to SWI. These timings describe the isolated slot-reuse
patch on `c1a2ee3`, before subsequent diagnostic and CLP updates on `main`.

## Profile before implementation

The baseline is `c1a2ee3eee8a88734c2ec8e6f28a5dae1225a349`, the current Core with
mutable CLP propagation. A fresh archived checkout was built with GHC 9.8.2,
`-O2 --enable-profiling --profiling-detail=late`. Each profile used 64 checked
queries through the unchanged `bench/core-major.hs` runner.

The [profile data](../data/jsonl/engine-slots-profile-2026-10-18.jsonl) retains
the header, complete `coreSolve` subtree, entries, allocation percentages,
binary identity and checked runner result. Whole-process profiles also contain
the separate Reference oracle and native preflight. The following self-time
percentages are normalized to the timed `coreSolve` subtree; they are approximate
sampling attribution, not additional uninstrumented timing measurements.

| Cost centre | Reverse | Loop |
| --- | ---: | ---: |
| Goal dispatch (`step'`) | 25.0% | 37.7% |
| Compound head matching | 15.8% | - |
| Head matcher | 11.4% | 6.0% |
| Arithmetic evaluation (`evalFast`) | - | 15.7% |
| Clause entry (`tryClause`) | 4.6% | 8.7% |
| Clause dispatch | 6.2% | 5.8% |

The reverse Core subtree entered 3,593,984 clauses and matched 13,787,712 head
patterns across its 64 queries. Loop entered 5,760,064 clauses and performed
28,800,000 fast arithmetic evaluations. This supported working on activation
costs, while also showing that slot allocation alone cannot remove most of the
dispatch, matching and arithmetic work.

## Implementation and safety

The [design note](../../engine/reusable-slots-2026-10-18.md) specifies ownership
and refusal conditions. The compiler records which slots need initialization;
first head occurrences write directly. An escaping unbound operand acquires a
stable variable cell with the same logical ID. Numeric results stay local.
Variable unification uses logical age because physical frame addresses can be
recycled. The head occurs check likewise uses fresh logical identity.

After outgoing arguments are materialized, a final ordinary call may reuse its
frame only if its selected clause fits, no continuation needs the frame, and
the newest choice point cannot restore it. A collection invalidates that reuse
offer. Backtracking, constraint watches and copied answers keep stable cells.
This implements reuse between tail activations; it does not color lifetimes
within a clause or move the driver to a separate native register stack.

An [untimed native counter probe](../data/jsonl/engine-slots-counters-2026-10-18.jsonl)
records actual executions of the original queries, without the timing runner's
unused nonce roots:

| Query | Fresh activation frames | Reused tail frames | Reused slot cells |
| --- | ---: | ---: | ---: |
| Loop 90,000 | 1 | 90,000 | 179,999 |
| Reverse workload | 8,994 | 47,162 | 179,252 |

These counters are disabled during ordinary solving and timed measurements.
They count activation storage operations, not all allocations or bytes of RSS.
The ground loop can reuse the same activation; escaping terms and variables
still need storage, and the initial heap array capacity is unchanged.

## Checked comparisons

The host is macOS arm64, with GHC 9.8.2 `-O2`, SWI-Prolog 10.0.2 and Scryer
`cargo:0.10.0`. There is one untimed validation round followed by five measured
fresh-process rounds. Engine order rotates within each workload. Each reverse
and loop batch contains 256 queries, comfortably above the external timer's
50 ms CPU gate. Table entries are medians in milliseconds per query.

| Workload | Core before | Core after | SWI | Scryer |
| --- | ---: | ---: | ---: | ---: |
| Reverse 30-element lists 100 times, then return a checked reverse | 8.427 | 9.445 | 0.833 | 2.965 |
| Counting loop to 90,000 | 10.253 | 9.812 | 1.811 | 8.082 |

The new Core is **11.33x SWI / 3.19x Scryer** on reverse and
**5.42x SWI / 1.21x Scryer** on loop. Reverse therefore remains outside the
roughly-2x target relative to either external engine. Measured Core ranges are
8.402-8.495 ms before and 9.295-9.673 ms after on reverse; loop is
10.194-10.354 ms before and 9.644-9.993 ms after.

GHC allocation per query rises from 35.129 to 36.934 MiB on reverse (+5.1%),
and 32.214 to 34.269 MiB on loop (+6.4%). Fewer Core frame allocations do not
imply less GHC allocation. Stable-variable promotion and operand/frame handling
remain costs of this implementation, alongside the dominant goal driver work.
The profiles support those remaining cost categories; they do not isolate a
precise percentage of the normal-build regression attributable to each change.

Other checked workloads keep the same source algorithms and independent result
models. Percentages below compare the five-sample medians; small differences
are local observations rather than portable performance guarantees.

| Workload | Before ms | After ms | CPU change | GHC allocation change |
| --- | ---: | ---: | ---: | ---: |
| Controls | 0.1430 | 0.1464 | +2.4% | +0.1% |
| Guards | 2.0861 | 2.1621 | +3.6% | +3.9% |
| Deep indexing | 4.8617 | 4.9685 | +2.2% | +3.0% |
| Liveness | 13.2314 | 13.3157 | +0.6% | +5.6% |
| 16-node table cycle | 0.0503 | 0.0522 | +3.9% | +0.1% |
| 240-node table cycle | 0.8707 | 0.8843 | +1.6% | +0.5% |
| Fibonacci 25 | 42.8257 | 45.0265 | +5.1% | +14.0% |
| First 8-queens solution | 8.9867 | 9.0319 | +0.5% | -3.4% |
| Breadboard RC | 1.6628 | 1.6754 | +0.8% | +0.5% |
| Breadboard divider | 2.0807 | 2.1165 | +1.7% | +0.5% |
| Breadboard triangle | 4.2040 | 4.1800 | -0.6% | +0.3% |
| Breadboard wide | 10.8361 | 10.9868 | +1.4% | +0.1% |
| 16x16 Minesweeper | 22.5640 | 22.6373 | +0.3% | +0.9% |

Startup, parsing and program loading are outside these loaded-query clocks.
Infera still compiles query plans, creates fresh query state, projects results
and checks the oracle/model in its timed invocation. SWI/Scryer execute a loaded
program and independently validate every result. The reverse/loop comparison
fully drains each explicitly `once`-bounded query. Output happens after timing. SWI uses
`statistics(process_cputime)`, including GC; Scryer's `library(time)` reports
CPU to three decimal places and supplies no loaded wall time here. The old
GC-excluding SWI compatibility clock is not used.

The allocation delta includes final RTS sampling/forced-GC bookkeeping outside
the CPU interval. GHC maximum residency includes the process's Reference
oracle and preflight; neither statistic is a Core-only live-cell or RSS bound.
These loaded results must not be compared directly to the older CLI reverse
case, which performs 3,000 repetitions and includes startup/loading.

## Correctness and reproduction

The original measured snapshot passed **440 properties / 27,677 cases in 44 groups**. The added suite checks
exact projected variable IDs, freshness, ordered errors/output, residuals,
escaping aliases, changing frame sizes, nested/repeated head constructors,
occurs-check failures, retained answers, scalar bits, CLP and control rollback.
Its native runs reject abandonment and use collection limits 1, 16 and default.
Counters verify loop/reverse reuse and refusal for a saved same-frame choice.

The existing dead-graph test now uses explicit temporary constructors to force
collection: a reusable ground spin no longer necessarily allocates. Its live
graph and reclamation assertions remain in force. All **477** inline example
and fixture queries agree with Reference and the earlier machine under forced
collection, with no fallback or skips. CLI acceptance, **61** editor tests and
**56** harness tests pass. [Validation logs](../data/jsonl/engine-slots-validation-2026-10-18.jsonl)
record commands, binary identities and complete output. The source package
includes the new tests, helpers and evidence. `cabal check` succeeds with its
existing optimization and dependency-upper-bound warnings.

The nonprofiling timing runner is byte-identical before and after. The new
`bench/core-external.pl` preserves the `bench/bench.pl` algorithms byte-for-byte;
`bench/core_external.py` builds commands and validates CPU markers, complete
answers and independent models. Its 22 new tests check those measurement
contracts. Run them with:

```sh
python3 -m unittest discover -s test -p '*bench_harness_test.py'
```

Build and run the normal Core cases with:

```sh
cabal build bench:core-major --offline --enable-optimization=2
cabal bench core-major --offline --enable-optimization=2 --benchmark-options='--case core-loop --batch 256 --timeout 60 +RTS -T -RTS'
```

Use the external commands documented in `bench/core_external.py`, with batch
256 for reverse and loop. Preserve the same optimized library/executable build
profile when repeating comparisons. The normal baseline binary was archived
before changes, separately from its instrumented profiling build.

The baseline runtime SHA-256 is
`47864b82eefdb35382e8de1913cfdbdf733db5b2cd2d4106825a6399ee6ad405`;
the measured working-tree runtime is
`98d3ce5ad8089955268893ee12c63914010f6e05437ecdbf9b96930728afdcfb`.
These hash sorted runtime source paths, NUL, file contents, NUL. The corresponding
normal `core-major` binary hashes are
`795089937a30a866b9cd5d0e11fee14c671993e618a1e73a52b198c0033beac6`
and `17a7a7bf1ec378f799de5c09f0a1e3eb97690b3b1f2db373d4b105cfec4a910d`.

[All samples](../data/jsonl/engine-slots-2026-10-18.jsonl) retain the validation
round and all five measurement rounds, complete checked output, commands,
allocation and CPU observations. [Provenance](../data/jsonl/engine-slots-provenance-2026-10-18.jsonl)
includes source/binary hashes, versions and the complete serial orchestrator.
Both source trees and all binaries were checked unchanged after timing. No
intermediate diagnostic-build timings enter these comparisons.

## Integration recheck before commit

After the timing run, `main` advanced to `bd13a9b` with diagnostic and CLP offset
equality updates. The combined tree was rebuilt in a fresh isolated Cabal
directory and passed **443 properties / 28,577 cases**, **487** forced-collection
parity queries, CLI acceptance, **61** editor tests and **56** harness tests.
Parity covers all Core fixtures and the acceptance examples present at the
measurement baseline, with no fallback or skips. A separate blanket run through
the newly added long demo programs was stopped after 181 seconds; their full
searches are outside this integration claim.

The initial shared build cache registered an older library directory despite
compiling newer optimized objects. An isolated package database resolved the
diagnostic/CLP test mismatch without runtime source changes.
[Integration commands, binary hashes and complete passing logs](../data/jsonl/engine-slots-integration-2026-10-18.jsonl)
record the combined runtime SHA-256:
`23884b92212479a52824c75db5d56dfb7adf72fab071bae7859878ed85248532`.
The benchmark tables above remain measurements of the earlier slot-reuse
snapshot; no refreshed timing claim is made for the combined tree.
