# Infera documentation

| Start here | Contents |
| --- | --- |
| [Language and tooling reference](website/index.html) | Installation, syntax, declarations, builtins, constraints and editor support; also [published online](https://hyperswine.github.io/NeoProlog/) |
| [Current engine](engine/README.md) | Default query execution, contracts, collection and compatibility boundaries |
| [Performance](performance/README.md) | Latest checked measurements and their scope |
| [Performance reports](performance/reports/README.md) | Dated implementation reports, including earlier machine/bytecode stages |
| [Raw benchmark data](performance/data/README.md) | Original measurements, separated by file format |
| [Dash docset](dash/README.md) | Build and subscribe to the offline reference |

```text
docs/
  README.md                 this index
  engine/                   current design, contracts and implementation history
  performance/
    README.md               results and measurement scope
    reports/                dated reports and acceptance records
    data/
      README.md             data conventions
      jsonl/                structured sample records
      tsv/                  tabular measurements
  website/                  static reference published by GitHub Pages
  dash/                     Dash docset builder and release feed
```

The engine guide describes the current default. Dated reports preserve the
state and acceptance gates of their respective revisions; statements there
about a default backend or pending work are historical. Raw measurements
keep their original names and contents, including recorded commands, hashes
and source paths.
