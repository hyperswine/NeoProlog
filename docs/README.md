# Infera documentation

| Start here | Contents |
| --- | --- |
| [Language and tooling reference](website/index.html) | Installation, syntax, declarations, builtins, constraints and editor support; also [published online](https://hyperswine.github.io/NeoProlog/) |
| [Current engine](2026-10-17-ENGINE.md) | Default query execution, contracts, collection and compatibility boundaries |
| [Performance](2026-10-15-PERFORMANCE.md) | Latest checked measurements and their scope |
| [Next optimization priorities](2026-10-31-OPTIMIZATION-FOLLOWUP.md) | Open lifetime, allocation and performance-gate work with acceptance criteria |
| [Raw benchmark data](data/README.md) | Original measurements, separated by file format |
| [Dash docset](dash/README.md) | Build and subscribe to the offline reference |

```text
docs/
  README.md                 this index
  YYYY-MM-DD-NAME.md        design notes and reports, one page per topic
  data/
    README.md               data conventions
    jsonl/                  structured sample records
    tsv/                    tabular measurements
  website/                  static reference published by GitHub Pages
  dash/                     Dash docset builder and release feed
```

## A chronological record

Every design note and report is named `YYYY-MM-DD-NAME.md`, dated by the day
it was first written, so a listing of this directory is the timeline of the
engine. Dated reports preserve the state and acceptance gates of their
revisions; statements there about a default backend or pending work are
historical. When two pages disagree, the later date wins, unless the earlier
page is a living page below. Raw measurements keep their original names and
contents, including recorded commands, hashes and source paths, so some of
those commands still name the `docs/performance/` paths used before
2026-10-24.

To add a page, name it with today's date and add a line to the end of the
table below. Do not rename a page when it changes; record later updates in a
dated section inside it.

### Living pages

These are kept current rather than superseded. Their date is when they began.

| page | what it holds |
|---|---|
| [2026-10-17-ENGINE](2026-10-17-ENGINE.md) | the current default engine: query execution, contracts, compatibility boundaries |
| [2026-10-15-PERFORMANCE](2026-10-15-PERFORMANCE.md) | the latest checked measurements, newest first |

### The record, oldest first

Pages named `ENGINE-...` were the performance reports, and the others the
engine design notes, before 2026-10-24.

| date | page | what it is |
|---|---|---|
| 2026-10-16 | [ENGINE-ROADMAP](2026-10-16-ENGINE-ROADMAP.md) | the earlier plan from a lazy-list resolver to an abstract machine; its backend decisions are historical |
| 2026-10-16 | [ENGINE-STEP1-ACCEPTANCE](2026-10-16-ENGINE-STEP1-ACCEPTANCE.md) | earlier machine: initial acceptance and the Step 2 handoff |
| 2026-10-16 | [ENGINE-STEP2-FOUNDATION](2026-10-16-ENGINE-STEP2-FOUNDATION.md) | earlier machine: regression repair and the first compiler slice |
| 2026-10-16 | [ENGINE-STEP2-HEAD-REGISTER](2026-10-16-ENGINE-STEP2-HEAD-REGISTER.md) | earlier machine: compiled head matching and register sharing |
| 2026-10-16 | [ENGINE-STEP2-LIFETIMES](2026-10-16-ENGINE-STEP2-LIFETIMES.md) | earlier machine: register lifetimes and incremental body allocation |
| 2026-10-16 | [ENGINE-STEP2-CONTROL](2026-10-16-ENGINE-STEP2-CONTROL.md) | earlier machine: compiled controls and cut barriers |
| 2026-10-16 | [ENGINE-STEP2-CACHE](2026-10-16-ENGINE-STEP2-CACHE.md) | earlier machine: predicate code caching and dispatch |
| 2026-10-16 | [ENGINE-STEP2-OPERANDS](2026-10-16-ENGINE-STEP2-OPERANDS.md) | earlier machine: operand materialization and invocation dispatch |
| 2026-10-17 | [ENGINE-STEP2-BUILTIN-OPERANDS](2026-10-17-ENGINE-STEP2-BUILTIN-OPERANDS.md) | earlier machine: typed arithmetic and CLP builtin operands |
| 2026-10-17 | [ENGINE-STEP2-OPAQUE-CONTROLS](2026-10-17-ENGINE-STEP2-OPAQUE-CONTROLS.md) | earlier machine: opaque control restoration and engine comparisons |
| 2026-10-17 | [LEGACY-MACHINE-VALIDATION](2026-10-17-LEGACY-MACHINE-VALIDATION.md) | validation detail for the earlier machine and bytecode backend |
| 2026-10-17 | [ENGINE-DIAGNOSIS](2026-10-17-ENGINE-DIAGNOSIS.md) | engine diagnosis and the plan to migrate to the Core |
| 2026-10-17 | [CONTRACTS-PERFORMANCE](2026-10-17-CONTRACTS-PERFORMANCE.md) | sorts, modes and determinism as performance: the proof rules and their effect |
| 2026-10-17 | [ENGINE-REVERSE](2026-10-17-ENGINE-REVERSE.md) | Core: reverse hot path, construction, matching and collection |
| 2026-10-18 | [MAJOR-DESIGN](2026-10-18-MAJOR-DESIGN.md) | design: four further Core performance designs |
| 2026-10-18 | [ENGINE-MAJOR](2026-10-18-ENGINE-MAJOR.md) | report: the four Core designs, first implementation and measurements |
| 2026-10-18 | [MUTABLE-CLP](2026-10-18-MUTABLE-CLP.md) | design: mutable CLP propagation in the Core |
| 2026-10-18 | [ENGINE-MUTABLE-CLP](2026-10-18-ENGINE-MUTABLE-CLP.md) | report: mutable CLP propagation, implementation and measurements |
| 2026-10-18 | [OFFSET-EQUALITY](2026-10-18-OFFSET-EQUALITY.md) | domain-consistent offset equalities |
| 2026-10-18 | [REUSABLE-SLOTS](2026-10-18-REUSABLE-SLOTS.md) | design: Core operand slots and tail frames |
| 2026-10-18 | [ENGINE-SLOTS](2026-10-18-ENGINE-SLOTS.md) | report: Core profiling, reusable slots and tail frames |
| 2026-10-18 | [ENGINE-EXTERNAL](2026-10-18-ENGINE-EXTERNAL.md) | the current Core against SWI-Prolog and Scryer |
| 2026-10-19 | [CONTROL-STACKS](2026-10-19-CONTROL-STACKS.md) | answers up to renaming, plain calls and the choice stack |
| 2026-10-19 | [CLAUSE-SELECTION](2026-10-19-CLAUSE-SELECTION.md) | allocation-free Core clause selection |
| 2026-10-19 | [ARITH-PLANS](2026-10-19-ARITH-PLANS.md) | compiled arithmetic plans for `is` and comparisons |
| 2026-10-20 | [PER-CALL-COSTS](2026-10-20-PER-CALL-COSTS.md) | where the Core's time per call goes |
| 2026-10-29 | [WAM-JIT](2026-10-29-WAM-JIT.md) | design: pinned stable store, WAM instruction stream, Sol-style native JIT of deterministic predicates |
| 2026-10-29 | [PINNED-STORE](2026-10-29-PINNED-STORE.md) | report: Step 1 of WAM-JIT, pinned ForeignPtr blocks with register-cached base pointers |
| 2026-10-30 | [WAM-STREAM](2026-10-30-WAM-STREAM.md) | report: Step 2 of WAM-JIT, load-time compilation and the clause instruction stream |
| 2026-10-30 | [JIT-ACTIVATION](2026-10-30-JIT-ACTIVATION.md) | report: the three defects that kept every native kernel from running, the occurs-check and trailing fixes they exposed, the cost of entering a kernel, and where the tree path's per-call allocation is not |
| 2026-10-31 | [OPTIMIZATION-FOLLOWUP](2026-10-31-OPTIMIZATION-FOLLOWUP.md) | next priorities: boxed-value reclamation, JIT mapping and image-cache ownership, interpreter allocation, and regression gates |
| 2026-11-04 | [NEXT-HORIZONS](2026-11-04-NEXT-HORIZONS.md) | roadmap and record of Horizons 1-5 as merged, with the corrections made after the merge |
| 2026-11-04 | [UNIFICATION-HEAVY](2026-11-04-UNIFICATION-HEAVY.md) | zebra, deriv and primes against SWI: profile, the Horizon 2 pruning removed, ranked remaining wins |
| 2026-11-05 | [BENCHMARKS](2026-11-05-BENCHMARKS.md) | report: every benchmark by task type, JIT on and off, against SWI-Prolog and Scryer on an Apple M4 |
| 2026-11-05 | [CHOICE-POINTS](2026-11-05-CHOICE-POINTS.md) | determinism of repeated head vars against `<`/`>`, selection guard for repeated head vars, inline simple if-then-else tests |
| 2026-11-05 | [FIRST-ARG-LOOKUP](2026-11-05-FIRST-ARG-LOOKUP.md) | linear fact-table exclusivity and module-load accumulation (-80% on 2000-fact lookup) |
| 2026-11-05 | [PER-CALL-WORK](2026-11-05-PER-CALL-WORK.md) | shallow backtracking, structures built in place, selection that only narrows; zebra -16%, deriv -11%, primes -8% instructions |
| 2026-11-05 | [SCAN-KERNEL](2026-11-05-SCAN-KERNEL.md) | native list-search kernels for `mem`/`right_of`-shaped predicates, choice points through the step clause; zebra -69% instructions |
| 2026-11-05 | [UNIFICATION-REFACTOR](2026-11-05-UNIFICATION-REFACTOR.md) | design: compiled write mode and static occurs elision, deferred `saveArgs`, single-pass decision trees, unboxed control stack, stream JIT |
| 2026-11-05 | [FILTER-KERNEL](2026-11-05-FILTER-KERNEL.md) | `remove/3` compiled natively: floored `%`, `k is E` guards, clause exclusivity through shared expressions; primes -90% instructions, 4.6x faster than SWI-Prolog |
| 2026-11-05 | [BINDREF-TRAIL-ORDER](2026-11-05-BINDREF-TRAIL-ORDER.md) | fix: `JBindRef` checks trail room and trails before writing the cell, so a full-trail bailout leaves nothing untrailed |
| 2026-11-05 | [BENCHMARKS-EVENING](2026-11-05-BENCHMARKS-EVENING.md) | report after the list kernels: primes 5x faster than SWI-Prolog, zebra 1.26x, deriv 4.2x behind; fix for a unify/occurs allocation regression (fib -32% allocation); choice-point copying measured at 2% |
| 2026-11-05 | [SHARED-EXCLUSIVITY](2026-11-05-SHARED-EXCLUSIVITY.md) | fix: the JIT no longer skips a later clause that could raise (`%` by zero); JIT accepts clause pairs inference proves exclusive |
| 2026-11-06 | [CLAUSE-COMPILER](2026-11-06-CLAUSE-COMPILER.md) | design: compile whole clauses to native code (native local stack, choice points that outlive a call, pause and resume, call-outs); four increments, det islands first |
