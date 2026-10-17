# Raw benchmark measurements

| Directory | Format and contents |
| --- | --- |
| [jsonl/](jsonl/) | JSON Lines: process results, individual samples, hashes, machine metadata and validation status |
| [tsv/](tsv/) | Tab-separated tables: engine comparisons, application checks and repeated experiments |

Names retain the implementation stage, workload and date. The
[reports](../reports/README.md) explain which samples are comparable and
which failed or superseded attempts must be excluded from conclusions.

These files were moved without changing their contents. Recorded commands,
absolute paths and source-hash keys describe the original run, so some
mention paths from before the documentation reorganization. Resolve files
using the report's current links; do not rewrite historical records to make
their embedded paths look current.

Save new structured samples in `jsonl/`, tab-separated exports in `tsv/`,
and any future comma-separated exports in a `csv/` subdirectory. This
repository currently has no CSV benchmark files. Include the workload,
revision, build profile, validation method and timing scope in the report
that introduces a new dataset.
