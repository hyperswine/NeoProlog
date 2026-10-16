// server.js — Language Server for Infera v2 (.nprolog / .infera)
//
// Features: semantic tokens, hover, go-to-definition, references, document
// symbols, completion, compiler-owned live diagnostics, and module-aware
// navigation through neoprolog.conf. JavaScript extracts symbols but never
// validates the language.
'use strict'

const {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  DidChangeConfigurationNotification,
  TextDocumentSyncKind,
  SymbolKind,
  MarkupKind,
  Location,
  Range,
  DiagnosticSeverity,
  CompletionItemKind
} = require('vscode-languageserver/node')

const { TextDocument } = require('vscode-languageserver-textdocument')
const fs = require('fs')
const path = require('path')
const os = require('os')
const { execFile } = require('child_process')
const { pathToFileURL, fileURLToPath } = require('url')

const analysis = require('./analysis')
const { compilerDiagnostics, visibleDiagnostics } = require('./checker')
const { tokenize, analyzeDocument, BUILTIN_DOCS, DECL_DOCS, BUILTIN_PREDICATES, KEYWORD_ATOMS, DET_WORDS, FLAG_WORDS, SORT_WORDS, TOKEN_TYPES, TOKEN_MODIFIERS, TT, TM } = analysis

const connection = createConnection(ProposedFeatures.all)
const documents = new TextDocuments(TextDocument)

let hasConfigurationCapability = false
let hasWorkspaceFolderCapability = false
let hasSemanticTokenRefreshCapability = false
const workspaceFolderPaths = []

const DEFAULT_SETTINGS = { executable: 'infera', checkOnSave: true, checkOnChange: true, performanceHints: true }
let globalSettings = { ...DEFAULT_SETTINGS }

// ─── neoprolog.conf ────────────────────────────────────────────────────────────

function parseConf(confPath) {
  const map = new Map()
  let raw
  try { raw = fs.readFileSync(confPath, 'utf8') } catch { return map }
  for (const line of raw.split(/\r?\n/)) {
    const t = line.trim()
    if (!t || t.startsWith('#')) continue
    const sp = t.indexOf(' ')
    if (sp < 0) continue
    map.set(t.slice(0, sp).trim(), t.slice(sp + 1).trim())
  }
  return map
}

const CONF_NAMES = ['neoprolog.conf', 'infera.conf', 'nprolog.conf']

function pickConfInDir(dir) {
  for (const n of CONF_NAMES) {
    const p = path.join(dir, n)
    if (fs.existsSync(p)) return p
  }
  return null
}

function findConfFile(startDir) {
  for (const wf of workspaceFolderPaths) {
    const c = pickConfInDir(wf)
    if (c) return c
  }
  let dir = startDir
  const root = path.parse(dir).root
  while (dir !== root) {
    const c = pickConfInDir(dir)
    if (c) return c
    const parent = path.dirname(dir)
    if (parent === dir) break
    dir = parent
  }
  return null
}

const confCache = new Map()

function getModuleConf(filePath) {
  const confPath = findConfFile(path.dirname(filePath))
  if (!confPath) return new Map()
  if (!confCache.has(confPath)) confCache.set(confPath, parseConf(confPath))
  return confCache.get(confPath)
}

// ─── External files ────────────────────────────────────────────────────────────

const externalCache = new Map()

function getExternalAnalysis(absPath) {
  const open = documents.get(pathToUri(absPath))
  if (open) return getAnalysis(open.uri) || refreshDocument(open)
  if (externalCache.has(absPath)) return externalCache.get(absPath)
  let text
  try { text = fs.readFileSync(absPath, 'utf8') } catch { return null }
  const a = analyzeDocument(text)
  externalCache.set(absPath, a)
  return a
}

function resolveModuleFile(alias, imports, currentFilePath) {
  if (!currentFilePath) return null
  const conf = getModuleConf(currentFilePath)
  for (const imp of imports) {
    if (imp.alias !== alias) continue
    if (conf.has(imp.modId)) return conf.get(imp.modId)
  }
  return null
}

function pathToUri(p) { return pathToFileURL(p).toString() }
function uriToPath(uri) { try { return fileURLToPath(uri) } catch { return null } }

// ─── Per-document state ────────────────────────────────────────────────────────

const documentCache = new Map()   // uri -> analysis
const checkerDiagnostics = new Map() // uri -> diagnostics from `infera check`
const checkerRuns = new Map()
const checkerTimers = new Map()
const checkerProcesses = new Map()
const documentVersions = new Map()
let checkerSerial = 0

function refreshDocument(document) {
  const a = analyzeDocument(document.getText())
  documentCache.set(document.uri, a)
  return a
}

function getAnalysis(uri) { return documentCache.get(uri) || null }

function locToRange(loc) { return Range.create(loc.line, loc.col, loc.line, loc.col + loc.length) }

function publish(uri) {
  connection.sendDiagnostics({ uri, version: documents.get(uri)?.version,
    diagnostics: checkerDiagnostics.get(uri) || [] })
}

// ─── `infera check` integration ───────────────────────────────────────────────

async function getSettings() {
  if (!hasConfigurationCapability) return globalSettings
  try {
    const s = await connection.workspace.getConfiguration('infera')
    return { ...DEFAULT_SETTINGS, ...(s || {}) }
  } catch {
    return globalSettings
  }
}

function invalidateCheck(uri) {
  const run = ++checkerSerial
  checkerRuns.set(uri, run)
  clearTimeout(checkerTimers.get(uri))
  checkerTimers.delete(uri)
  const child = checkerProcesses.get(uri)
  checkerProcesses.delete(uri)
  if (child) child.kill()
  checkerDiagnostics.delete(uri)
  return run
}

function queueCheck(uri, reason, delay = 200) {
  const run = invalidateCheck(uri)
  publish(uri)
  checkerTimers.set(uri, setTimeout(() => {
    checkerTimers.delete(uri)
    runChecker(uri, run, reason)
  }, delay))
}

function checkerFailure(uri, message) {
  checkerDiagnostics.set(uri, [{ range: Range.create(0, 0, 0, 1),
    severity: DiagnosticSeverity.Warning, code: 'checker-unavailable',
    source: 'infera checker', message }])
  publish(uri)
}

async function runChecker(uri, run, reason) {
  // Untitled documents have no disk identity yet. Give the compiler a virtual
  // path in the workspace for import context; source always comes from stdin.
  const filePath = uriToPath(uri) || (uri.startsWith('untitled:')
    ? path.join(workspaceFolderPaths[0] || process.cwd(), `.infera-${encodeURIComponent(uri)}.nprolog`) : null)
  if (!filePath || !documents.get(uri) || checkerRuns.get(uri) !== run) return
  const version = documents.get(uri)?.version
  const current = () => documents.get(uri)?.version === version && checkerRuns.get(uri) === run
  let temporary
  try {
    const settings = await getSettings()
    if (!current()) return
    const enabled = reason === 'save' ? settings.checkOnSave
      : reason === 'change' ? settings.checkOnChange : settings.checkOnSave || settings.checkOnChange
    if (!enabled) return
    const source = documents.get(uri).getText()
    const buffers = documents.all().filter(doc => doc.uri !== uri && uriToPath(doc.uri))
      .map(doc => ({ path: uriToPath(doc.uri), text: doc.getText() }))
    const args = ['check', '--json', '--stdin', filePath]
    if (buffers.length) {
      temporary = await fs.promises.mkdtemp(path.join(os.tmpdir(), 'infera-buffers-'))
      for (const [i, buffer] of buffers.entries()) {
        const snapshot = path.join(temporary, String(i))
        await fs.promises.writeFile(snapshot, buffer.text, 'utf8')
        args.push('--buffer', buffer.path, snapshot)
      }
    }
    if (!current()) return
    const confPath = findConfFile(path.dirname(filePath))
    const cwd = confPath ? path.dirname(confPath) : path.dirname(filePath)
    await new Promise(resolve => {
      const child = execFile(settings.executable, args, { cwd, timeout: 15000, maxBuffer: 4 * 1024 * 1024 }, (err, stdout, stderr) => {
        if (checkerProcesses.get(uri) === child) checkerProcesses.delete(uri)
        if (!current()) { resolve(); return }
        try {
          if (err && (err.killed || typeof err.code !== 'number')) throw err
          const diags = compilerDiagnostics(stdout, filePath)
          if (err && !diags.some(d => d.severity === DiagnosticSeverity.Error)) throw err
          checkerDiagnostics.set(uri, visibleDiagnostics(diags, settings))
          publish(uri)
        } catch (failure) {
          connection.console.error(`infera check --json failed: ${stderr || failure.message}`)
          checkerFailure(uri, `Compiler diagnostics unavailable. Check infera.executable and use a compiler supporting check --json --stdin. ${failure.code === 'ENOENT' ? 'Executable not found.' : failure.killed ? 'Check timed out.' : 'Check failed.'}`)
        }
        resolve()
      })
      checkerProcesses.set(uri, child)
      // A superseded/failed checker may close stdin before the write completes.
      child.stdin.on('error', () => {})
      child.stdin.end(source, 'utf8')
    })
  } catch (failure) {
    if (current()) checkerFailure(uri, `Compiler diagnostics unavailable: ${failure.message}`)
  } finally {
    if (temporary) await fs.promises.rm(temporary, { recursive: true, force: true }).catch(() => {})
  }
}

// ─── Cursor inspection ─────────────────────────────────────────────────────────

function getWordAt(lines, position) {
  const s = lines[position.line]
  if (s === undefined) return null
  const col = position.character
  let start = col, end = col
  while (start > 0 && /[a-zA-Z0-9_]/.test(s[start - 1])) start--
  while (end < s.length && /[a-zA-Z0-9_]/.test(s[end])) end++
  if (start === end) return null
  const word = s.slice(start, end)

  if (end < s.length && s[end] === ':' && s[end + 1] !== ':' && /[a-z]/.test(s[end + 1] || '')) {
    let pe = end + 1
    while (pe < s.length && /[a-zA-Z0-9_]/.test(s[pe])) pe++
    return { kind: 'module', mod: word, pred: s.slice(end + 1, pe), start, end }
  }
  if (start > 0 && s[start - 1] === ':' && (start < 2 || s[start - 2] !== ':') && /[a-z]/.test(word[0])) {
    let ms = start - 1
    while (ms > 0 && /[a-zA-Z0-9_]/.test(s[ms - 1])) ms--
    const mod = s.slice(ms, start - 1)
    if (mod && /[a-z]/.test(mod[0])) return { kind: 'predicate', mod, pred: word, start, end }
  }
  return { kind: 'plain', word, start, end }
}

function describeDefs(name, defs, decls, fileLabel) {
  const arities = [...new Set(defs.map(d => d.arity).filter(a => a !== null))]
  const label = arities.length === 1 ? `${name}/${arities[0]}` : name
  const lines = defs.map(d => d.line + 1).join(', ')
  const plural = defs.length === 1 ? 'clause' : 'clauses'
  let text = `**Predicate:** \`${label}\`\n\n${defs.length} ${plural}${fileLabel ? ` in \`${fileLabel}\`` : ''} at line${defs.length > 1 ? 's' : ''} ${lines}`
  if (decls && decls.length) {
    text += '\n\n```infera\n' + decls.map(d => d.text).join('\n') + '\n```'
  } else {
    text += '\n\n_No declaration: most general signature (any, <=>, nondet) unless inferred._'
  }
  return text
}

// ─── Semantic tokens ───────────────────────────────────────────────────────────

function buildSemanticTokens(a, filePath) {
  const { tokens, headPositions, queryPositions, namespacePositions, qualColonPositions, importKeyPositions, declNamePositions, declWordKinds, directivePositions } = a
  const data = []
  const predicateMods = analysis.predicateModifierPositions(a, alias => {
    const resolved = resolveModuleFile(alias, a.imports, filePath)
    return resolved ? getExternalAnalysis(resolved) : null
  })
  let prevLine = 0, prevCol = 0
  function push(line, col, length, type, mods) {
    const dl = line - prevLine
    const dc = dl === 0 ? col - prevCol : col
    data.push(dl, dc, length, type, mods)
    prevLine = line; prevCol = col
  }
  for (const tok of tokens) {
    const len = tok.text.length
    const key = `${tok.line}:${tok.col}`
    const declKind = declWordKinds.get(key)
    if (declKind) {
      const type = declKind === 'sort' ? TT.type : declKind === 'mode' ? TT.operator : TT.keyword
      push(tok.line, tok.col, len, type, 0)
      continue
    }
    switch (tok.type) {
      case 'comment': push(tok.line, tok.col, len, TT.comment, 0); break
      case 'string':
      case 'charlit': push(tok.line, tok.col, len, TT.string, 0); break
      case 'integer':
      case 'float': push(tok.line, tok.col, len, TT.number, 0); break
      case 'variable': push(tok.line, tok.col, len, TT.variable, 0); break
      case 'anon': push(tok.line, tok.col, len, TT.parameter, 0); break
      case 'neck':
      case 'dcgneck':
      case 'bang': push(tok.line, tok.col, len, TT.keyword, predicateMods.get(key) || 0); break
      case 'colon':
        push(tok.line, tok.col, len, qualColonPositions.has(key) ? TT.operator : TT.keyword, 0)
        break
      case 'op':
        push(tok.line, tok.col, len, queryPositions.has(key) ? TT.keyword : TT.operator, 0)
        break
      case 'semi':
      case 'opdot':
      case 'comma':
      case 'pipe':
      case 'dot':
        push(tok.line, tok.col, len, TT.operator, 0)
        break
      case 'atom':
        if (importKeyPositions.has(key) || directivePositions.has(key) || KEYWORD_ATOMS.has(tok.text)) {
          push(tok.line, tok.col, len, TT.keyword, predicateMods.get(key) || 0)
        } else if (namespacePositions.has(key)) {
          push(tok.line, tok.col, len, TT.namespace, 0)
        } else if (headPositions.has(key) || declNamePositions.has(key)) {
          push(tok.line, tok.col, len, TT.function, TM.declaration | (predicateMods.get(key) || 0))
        } else {
          push(tok.line, tok.col, len, TT.function, predicateMods.get(key) || 0)
        }
        break
      default: break
    }
  }
  return data
}

// ─── Initialisation ────────────────────────────────────────────────────────────

connection.onInitialize(params => {
  const caps = params.capabilities
  hasConfigurationCapability = !!(caps.workspace && caps.workspace.configuration)
  hasWorkspaceFolderCapability = !!(caps.workspace && caps.workspace.workspaceFolders)
  hasSemanticTokenRefreshCapability = !!caps.workspace?.semanticTokens?.refreshSupport
  if (params.workspaceFolders) {
    for (const f of params.workspaceFolders) {
      const p = uriToPath(f.uri)
      if (p) workspaceFolderPaths.push(p)
    }
  }
  return {
    capabilities: {
      textDocumentSync: { openClose: true, change: TextDocumentSyncKind.Incremental, save: { includeText: false } },
      hoverProvider: true,
      definitionProvider: true,
      referencesProvider: true,
      documentSymbolProvider: true,
      completionProvider: { triggerCharacters: [':', '('] },
      semanticTokensProvider: {
        legend: { tokenTypes: TOKEN_TYPES, tokenModifiers: TOKEN_MODIFIERS },
        full: true
      }
    }
  }
})

connection.onInitialized(() => {
  if (hasConfigurationCapability) {
    connection.client.register(DidChangeConfigurationNotification.type, undefined)
  }
  if (hasWorkspaceFolderCapability) {
    connection.workspace.onDidChangeWorkspaceFolders(event => {
      for (const added of event.added) {
        const p = uriToPath(added.uri)
        if (p && !workspaceFolderPaths.includes(p)) workspaceFolderPaths.push(p)
      }
      for (const removed of event.removed) {
        const p = uriToPath(removed.uri)
        const i = workspaceFolderPaths.indexOf(p)
        if (i >= 0) workspaceFolderPaths.splice(i, 1)
      }
    })
  }
})

connection.onDidChangeConfiguration(change => {
  if (!hasConfigurationCapability) {
    globalSettings = { ...DEFAULT_SETTINGS, ...((change.settings && change.settings.infera) || {}) }
  }
  for (const doc of documents.all()) queueCheck(doc.uri, 'open', 0)
})

// ─── Document events ───────────────────────────────────────────────────────────

documents.onDidOpen(e => {
  refreshDocument(e.document)
  // TextDocuments emits an initial content event immediately after open.
})

documents.onDidChangeContent(change => {
  const p = uriToPath(change.document.uri)
  if (p) externalCache.delete(p)
  refreshDocument(change.document)
  refreshSemanticTokens()
  const initial = !documentVersions.has(change.document.uri)
  documentVersions.set(change.document.uri, change.document.version)
  queueCheck(change.document.uri, initial ? 'open' : 'change')
  for (const doc of documents.all()) {
    if (doc.uri !== change.document.uri) queueCheck(doc.uri, 'change')
  }
})

documents.onDidSave(async () => {
  const versions = new Map(documents.all().map(doc => [doc.uri, doc.version]))
  const settings = await getSettings()
  // A disabled save check must not cancel an enabled live check, for example
  // when an editor autosaves immediately after sending a content change.
  if (!settings.checkOnSave) return
  for (const doc of documents.all()) {
    if (versions.get(doc.uri) === doc.version) queueCheck(doc.uri, 'save', 0)
  }
})

documents.onDidClose(e => {
  documentCache.delete(e.document.uri)
  documentVersions.delete(e.document.uri)
  invalidateCheck(e.document.uri)
  checkerRuns.delete(e.document.uri)
  connection.sendDiagnostics({ uri: e.document.uri, diagnostics: [] })
  refreshSemanticTokens()
  for (const doc of documents.all()) queueCheck(doc.uri, 'open')
})

connection.onDidChangeWatchedFiles(event => {
  for (const change of event.changes) {
    const p = uriToPath(change.uri)
    if (p && CONF_NAMES.includes(path.basename(p))) confCache.delete(p)
    if (p) externalCache.delete(p)
  }
  refreshSemanticTokens()
  for (const doc of documents.all()) queueCheck(doc.uri, 'open')
})

// ─── Hover ─────────────────────────────────────────────────────────────────────

connection.onHover(({ textDocument, position }) => {
  const document = documents.get(textDocument.uri)
  const a = getAnalysis(textDocument.uri)
  if (!document || !a) return null
  const lines = document.getText().split(/\r?\n/)
  const info = getWordAt(lines, position)
  if (!info) return null
  const filePath = uriToPath(textDocument.uri)
  const parts = []

  if (info.kind === 'module' || info.kind === 'predicate') {
    const { mod, pred } = info
    const imp = a.imports.find(i => i.alias === mod)
    if (info.kind === 'module') {
      parts.push(imp ? `**Module:** \`${mod}\`\n\nImported as \`${imp.modId}\`` : `**Module:** \`${mod}\` — not found in imports`)
    }
    if (pred) {
      const extPath = resolveModuleFile(mod, a.imports, filePath)
      if (extPath) {
        const ext = getExternalAnalysis(extPath)
        if (ext && ext.predicateDefs.has(pred)) {
          parts.push(describeDefs(`${mod}:${pred}`, ext.predicateDefs.get(pred), ext.decls.get(pred), path.basename(extPath)))
        } else {
          parts.push(`**Predicate:** \`${mod}:${pred}\` — not found in \`${path.basename(extPath)}\``)
        }
      } else {
        parts.push(`**Predicate:** \`${mod}:${pred}\` — module \`${mod}\` not resolved (check neoprolog.conf)`)
      }
    }
    return parts.length ? { contents: { kind: MarkupKind.Markdown, value: parts.join('\n\n---\n\n') } } : null
  }

  const { word } = info
  const key = `${position.line}:${info.start}`
  const declKind = a.declWordKinds.get(key)
  if (declKind && DECL_DOCS[word]) {
    parts.push(`**${declKind}:** \`${word}\`\n\n${DECL_DOCS[word]}`)
  } else if (BUILTIN_DOCS[word]) {
    parts.push(`**Built-in:** \`${word}\`\n\n${BUILTIN_DOCS[word]}`)
  }
  if (a.predicateDefs.has(word)) {
    parts.push(describeDefs(word, a.predicateDefs.get(word), a.decls.get(word), null))
  } else if (a.decls.has(word)) {
    parts.push(`**Declared:** \n\n\`\`\`infera\n${a.decls.get(word).map(d => d.text).join('\n')}\n\`\`\`\n\n_No clauses in this file._`)
  } else if (!BUILTIN_DOCS[word] && !declKind && a.predicateRefs.has(word)) {
    parts.push(`**Predicate:** \`${word}\` — not defined in this file`)
  }
  if (/^[A-Z_]/.test(word) && word !== '_') parts.push(`**Logic variable:** \`${word}\``)
  return parts.length ? { contents: { kind: MarkupKind.Markdown, value: parts.join('\n\n---\n\n') } } : null
})

// ─── Definition ────────────────────────────────────────────────────────────────

connection.onDefinition(({ textDocument, position }) => {
  const document = documents.get(textDocument.uri)
  const a = getAnalysis(textDocument.uri)
  if (!document || !a) return null
  const lines = document.getText().split(/\r?\n/)
  const info = getWordAt(lines, position)
  if (!info) return null
  const filePath = uriToPath(textDocument.uri)

  if (info.kind === 'module') {
    const imp = a.imports.find(i => i.alias === info.mod)
    if (imp) return Location.create(textDocument.uri, locToRange(imp))
    const extPath = resolveModuleFile(info.mod, a.imports, filePath)
    return extPath ? Location.create(pathToUri(extPath), Range.create(0, 0, 0, 0)) : null
  }
  if (info.kind === 'predicate') {
    const extPath = resolveModuleFile(info.mod, a.imports, filePath)
    if (!extPath) return null
    const ext = getExternalAnalysis(extPath)
    const defs = ext && ext.predicateDefs.get(info.pred)
    if (!defs || !defs.length) return null
    const extUri = pathToUri(extPath)
    return defs.map(d => Location.create(extUri, locToRange(d)))
  }
  const defs = a.predicateDefs.get(info.word) || []
  const decls = a.decls.get(info.word) || []
  const locs = [...decls, ...defs].map(d => Location.create(textDocument.uri, locToRange(d)))
  return locs.length ? locs : null
})

// ─── References ────────────────────────────────────────────────────────────────

connection.onReferences(({ textDocument, position, context }) => {
  const document = documents.get(textDocument.uri)
  const a = getAnalysis(textDocument.uri)
  if (!document || !a) return null
  const lines = document.getText().split(/\r?\n/)
  const info = getWordAt(lines, position)
  if (!info) return null
  const results = []

  if (info.kind === 'module' || info.kind === 'predicate') {
    for (const qr of (a.qualifiedRefs.get(info.mod) || [])) {
      if (!info.pred || qr.pred === info.pred) results.push(Location.create(textDocument.uri, locToRange(qr.predLoc)))
    }
    if (context.includeDeclaration && info.kind === 'module') {
      const imp = a.imports.find(i => i.alias === info.mod)
      if (imp) results.push(Location.create(textDocument.uri, locToRange(imp)))
    }
    return results
  }
  if (context.includeDeclaration) {
    for (const d of (a.decls.get(info.word) || [])) results.push(Location.create(textDocument.uri, locToRange(d)))
    for (const d of (a.predicateDefs.get(info.word) || [])) results.push(Location.create(textDocument.uri, locToRange(d)))
  }
  for (const r of (a.predicateRefs.get(info.word) || [])) results.push(Location.create(textDocument.uri, locToRange(r)))
  return results
})

// ─── Symbols ───────────────────────────────────────────────────────────────────

connection.onDocumentSymbol(({ textDocument }) => {
  const a = getAnalysis(textDocument.uri)
  if (!a) return []
  const symbols = []
  for (const [name, decls] of a.decls) {
    for (const d of decls) {
      symbols.push({ name: `${name}/${d.arity} (declaration)`, kind: SymbolKind.Interface, location: Location.create(textDocument.uri, locToRange(d)) })
    }
  }
  for (const [name, defs] of a.predicateDefs) {
    for (const d of defs) {
      const label = d.arity === null ? name : `${name}/${d.arity}`
      symbols.push({ name: label, kind: SymbolKind.Function, location: Location.create(textDocument.uri, locToRange(d)) })
    }
  }
  return symbols
})

// ─── Completion ────────────────────────────────────────────────────────────────

connection.onCompletion(({ textDocument, position }) => {
  const document = documents.get(textDocument.uri)
  const a = getAnalysis(textDocument.uri)
  if (!document || !a) return []
  const filePath = uriToPath(textDocument.uri)
  const lines = document.getText().split(/\r?\n/)
  const before = (lines[position.line] || '').slice(0, position.character)

  // mod: → predicates of that module
  const qual = before.match(/([a-z][a-zA-Z0-9_]*):$/)
  if (qual) {
    const extPath = resolveModuleFile(qual[1], a.imports, filePath)
    const ext = extPath && getExternalAnalysis(extPath)
    if (!ext) return []
    return [...ext.predicateDefs.keys()].map(name => {
      const defs = ext.predicateDefs.get(name)
      return {
        label: name,
        kind: CompletionItemKind.Function,
        detail: `${qual[1]}:${name} (${defs.length} clause${defs.length !== 1 ? 's' : ''} in ${path.basename(extPath)})`
      }
    })
  }

  // Inside a declaration: `name : ...`
  if (/^\s*[a-z][a-zA-Z0-9_]*\s*:\s/.test(before)) {
    const items = []
    const inParens = /\([^)]*$/.test(before)
    if (inParens) {
      for (const s of SORT_WORDS) items.push({ label: s, kind: CompletionItemKind.TypeParameter, detail: 'sort', documentation: { kind: MarkupKind.Markdown, value: DECL_DOCS[s] || '' } })
    } else {
      for (const d of DET_WORDS) items.push({ label: d, kind: CompletionItemKind.Keyword, detail: 'determinism', documentation: { kind: MarkupKind.Markdown, value: DECL_DOCS[d] } })
      for (const f of FLAG_WORDS) items.push({ label: f, kind: CompletionItemKind.Keyword, detail: 'flag', documentation: { kind: MarkupKind.Markdown, value: DECL_DOCS[f] } })
      for (const s of SORT_WORDS) items.push({ label: `(${s}: <=)`, kind: CompletionItemKind.Snippet, detail: 'argument spec', insertText: `(${s}: <=)` })
    }
    for (const m of ['<=', '=>', '<=>']) items.push({ label: m, kind: CompletionItemKind.Operator, detail: 'mode', documentation: { kind: MarkupKind.Markdown, value: DECL_DOCS[m] } })
    return items
  }

  const items = []
  const seen = new Set()
  for (const [name, defs] of a.predicateDefs) {
    seen.add(name)
    const arities = [...new Set(defs.map(d => d.arity).filter(x => x !== null))]
    const decl = a.decls.get(name)
    items.push({
      label: name,
      kind: CompletionItemKind.Function,
      detail: `${arities.map(x => `${name}/${x}`).join(', ') || name} (${defs.length} clause${defs.length !== 1 ? 's' : ''})`,
      documentation: decl ? { kind: MarkupKind.Markdown, value: '```infera\n' + decl.map(d => d.text).join('\n') + '\n```' } : undefined
    })
  }
  for (const imp of a.imports) {
    if (seen.has(imp.alias)) continue
    seen.add(imp.alias)
    items.push({ label: imp.alias, kind: CompletionItemKind.Module, detail: `module (${imp.modId})`, insertText: imp.alias + ':' })
  }
  for (const [name, doc] of Object.entries(BUILTIN_DOCS)) {
    if (seen.has(name) || !/^[a-z]/.test(name)) continue
    seen.add(name)
    items.push({ label: name, kind: CompletionItemKind.Keyword, detail: 'built-in', documentation: { kind: MarkupKind.Markdown, value: doc } })
  }
  return items
})

// ─── Semantic tokens ───────────────────────────────────────────────────────────

connection.languages.semanticTokens.on(({ textDocument }) => {
  const document = documents.get(textDocument.uri)
  if (!document) return { data: [] }
  let a = getAnalysis(textDocument.uri)
  if (!a) a = refreshDocument(document)
  return { data: buildSemanticTokens(a, uriToPath(textDocument.uri)) }
})

function refreshSemanticTokens() {
  if (hasSemanticTokenRefreshCapability) {
    connection.languages.semanticTokens.refresh().catch(() => {})
  }
}

documents.listen(connection)
connection.listen()
