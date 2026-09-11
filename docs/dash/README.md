# Infera Dash docset

`build.js` turns the static documentation in `../website` into a
[Dash](https://kapeli.com/dash) docset:

```
node docs/dash/build.js        # needs node and the sqlite3 CLI
```

It writes `docs/dash/dist/Infera.docset` and `docs/dash/dist/Infera.tgz`.
Every element in the site that carries a `data-dash="Type:Name"` attribute
becomes an index entry (and a table-of-contents anchor); every page becomes a
Guide entry.

## Adding to Dash

Either open `dist/Infera.docset` (double-click, or *Dash → Preferences →
Docsets → +*), or subscribe to the feed so updates arrive with releases:

```
dash-feed://https%3A%2F%2Fraw.githubusercontent.com%2Fhyperswine%2FNeoProlog%2Fmain%2Fdocs%2Fdash%2FInfera.xml
```

The `Release` workflow builds the docset on every `v*` tag and attaches
`Infera.tgz` to the GitHub release, which is what the feed points at.
