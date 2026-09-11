# Infera for VS Code

Language support for [Infera v2](https://github.com/hyperswine/NeoProlog)
(`.nprolog`, `.infera`).

- Syntax highlighting (TextMate grammar plus semantic tokens: clause heads,
  declarations, sorts, modes, module namespaces, queries).
- Hover: built-in docs, predicate clause counts and declared signatures,
  declaration keywords, imported modules.
- Go to definition / find references / document symbols, including
  `mod:pred` calls resolved through `neoprolog.conf`.
- Completion: local predicates, module aliases (`mod:` completes the
  module's predicates), built-ins, and declaration keywords, sorts and modes
  inside `name : ...` declarations.
- Diagnostics from static analysis: undefined predicates, calls with an
  arity no clause defines, declarations without clauses or with the wrong
  arity, malformed declarations, unknown directives, unbalanced brackets,
  missing terminators and singleton variables.
- Diagnostics from the real parser: when `infera` is on your `PATH` (or set
  `infera.executable`), `infera check <file>` runs on open and save and its
  errors are shown at the reported position.

## Install

```
cd lsp
npm install
npm run install-extension      # packages a .vsix and installs it into VS Code
```

Or package only (`npm run package`) and install the `.vsix` via
*Extensions → … → Install from VSIX*.

## Develop

```
npm test                       # unit tests for the analyser
```

`server/analysis.js` is the tokenizer and analyser (pure, testable);
`server/server.js` wires it to the LSP; `client/extension.js` is the VS Code
client.  Open this folder in VS Code and press F5 to launch an Extension
Development Host.

## Settings

| setting | default | meaning |
| --- | --- | --- |
| `infera.executable` | `infera` | binary used for `infera check` |
| `infera.checkOnSave` | `true` | run the parser check on open and save |
