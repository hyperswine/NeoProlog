# Infera documentation

| Start here | Contents |
| --- | --- |
| [Language and tooling reference](website/index.html) | Installation, syntax, declarations, builtins, constraints and editor support; also [published online](https://hyperswine.github.io/NeoProlog/) |
| [Current engine](2026-10-17-ENGINE.md) | Default query execution, contracts, collection and compatibility boundaries |
| [Performance](2026-10-15-PERFORMANCE.md) | Latest checked measurements and their scope |
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
