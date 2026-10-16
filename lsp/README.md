# Infera for VS Code

Language support for [Infera v2](https://github.com/hyperswine/NeoProlog)
(`.nprolog`, `.infera`).

- Syntax highlighting (TextMate grammar plus semantic tokens: clause heads,
  declarations, sorts, modes, module namespaces, queries). Declared `unsafe`
  and `dynamic` predicate names are underlined at declarations, heads and
  resolved calls, including imported predicates and statically known `call` or
  `phrase` targets. Effectful built-in calls are also underlined. Overloads are
  distinguished by arity; strings, comments and ordinary data atoms are excluded.
- Hover: built-in docs, predicate clause counts and declared signatures,
  declaration keywords, imported modules.
- Go to definition / find references / document symbols, including
  `mod:pred` calls resolved through `neoprolog.conf`.
- Completion: local predicates, module aliases (`mod:` completes the
  module's predicates), built-ins, and declaration keywords, sorts and modes
  inside `name : ...` declarations.
- Compiler-owned diagnostics: undefined predicates, call arities, declaration
  and literal-sort conflicts, singleton warnings, parser and import errors.
  `infera check --json --stdin` checks the current buffer on open, after a short
  edit debounce, and on save. Open imports use their unsaved contents too.
  Messages, codes, severities and source ranges match command-line checks.
  Imported errors link to their owning file, and superseded checks are cancelled.
  Untitled buffers use the workspace as their import context.
- Compiler performance suggestions use informational diagnostics, with the
  editor's blue styling. They suggest opportunities such as tail recursion,
  posting constraints before labeling, and useful clause indexing; they do not
  change whether a program passes checking. `infera.performanceHints` hides
  these suggestions independently of correctness diagnostics.
- A missing, incompatible or failing compiler produces an explicit availability
  warning. JavaScript supplies navigation and highlighting, with no independent
  validation or fallback diagnostic rules.

## Install

```
cd lsp
npm install
npm run install-extension      # packages a .vsix and installs it into VS Code
```

Or package only (`npm run package`) and install the `.vsix` via
*Extensions → … → Install from VSIX*.

After updating an installed extension, run **Developer: Reload Window** and
check that the file's language mode is **Infera**. Comments begin with `#`,
except for the CLP operators `#=`, `#!=`, `#<`, `#>`, `#<=`, and `#>=`.

If a machine still associates `.nprolog` files with the older **NeoProlog**
language, use **Change Language Mode → Configure File Association for
'.nprolog' → Infera**, or change its `files.associations` setting to
`"*.nprolog": "infera"`.

## Develop

```
npm test                       # TextMate highlighting, symbols, diagnostics and server tests
# Include the real-compiler integration test:
INFERA_BIN="$(cd .. && cabal list-bin exe:infera)" npm test
```

`server/analysis.js` is the tolerant tokenizer and symbol extractor (pure, testable);
`server/server.js` wires it to the LSP; `client/extension.js` is the VS Code
client.  Open this folder in VS Code and press F5 to launch an Extension
Development Host.

Highlighting tests use VS Code's TextMate and Oniguruma engine, and verify the
entire Minesweeper example against both grammar scopes and LSP semantic tokens.

## Settings

| setting | default | meaning |
| --- | --- | --- |
| `infera.executable` | `infera` | binary used for `infera check` |
| `infera.checkOnSave` | `true` | run the compiler check on save |
| `infera.checkOnChange` | `true` | run the compiler check on unsaved edits, after a short debounce |
| `infera.performanceHints` | `true` | show compiler suggestions whose code begins with `perf-` |

Opening a document checks it when either setting is enabled. Both can be
disabled to turn off diagnostics without changing highlighting or navigation.
The compiler must support `check --json --stdin` and `--buffer` source snapshots.

The extension enables semantic highlighting for Infera and contributes underline
defaults for `*.unsafe:infera` and `*.dynamic:infera`. Themes and user settings can
override these styles through `editor.semanticTokenColorCustomizations`; turning
off `editor.semanticHighlighting.enabled` also removes semantic underlines.
These markers describe declarations and effects, without adding warnings for
intentional use of `unsafe` or `dynamic`. Diagnostic colors follow the active
theme and editor settings. See VS Code's [semantic highlighting guide](https://code.visualstudio.com/api/language-extensions/semantic-highlight-guide#theming)
for supported style overrides.
