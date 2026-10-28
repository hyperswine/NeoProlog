'use strict'

const test = require('node:test')
const assert = require('node:assert/strict')
const fs = require('fs')
const os = require('os')
const path = require('path')
const { pathToFileURL } = require('url')
const { spawn, spawnSync } = require('child_process')
const { compilerDiagnostics } = require('../server/checker')

async function client(t, executable, settings = {}, workspaceRoot = null) {
  const child = spawn(process.execPath, [path.join(__dirname, '../server/server.js'), '--stdio'])
  t.after(() => child.kill())
  let buffer = Buffer.alloc(0), serial = 0
  const messages = [], pending = new Map()
  child.stdout.on('data', chunk => {
    buffer = Buffer.concat([buffer, chunk])
    for (;;) {
      const boundary = buffer.indexOf('\r\n\r\n')
      if (boundary < 0) break
      const length = Number(buffer.subarray(0, boundary).toString().match(/Content-Length: (\d+)/i)[1])
      if (buffer.length < boundary + 4 + length) break
      const message = JSON.parse(buffer.subarray(boundary + 4, boundary + 4 + length).toString())
      buffer = buffer.subarray(boundary + 4 + length)
      messages.push(message)
      if (pending.has(message.id)) { pending.get(message.id)(message); pending.delete(message.id) }
    }
  })
  const send = message => {
    const body = JSON.stringify(message)
    child.stdin.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`)
  }
  const request = (method, params) => new Promise(resolve => {
    const id = ++serial
    pending.set(id, resolve)
    send({ jsonrpc: '2.0', id, method, params })
  })
  const notify = (method, params) => send({ jsonrpc: '2.0', method, params })
  await request('initialize', { processId: null, rootUri: null, capabilities: {},
    workspaceFolders: workspaceRoot ? (Array.isArray(workspaceRoot) ? workspaceRoot : [workspaceRoot])
      .map((root, i) => ({ uri: pathToFileURL(root).href, name: `test${i}` })) : [] })
  notify('initialized', {})
  notify('workspace/didChangeConfiguration', { settings: { infera: { executable, checkOnSave: true, ...settings } } })
  return { notify, request, messages }
}

async function until(predicate) {
  const deadline = Date.now() + 10000
  while (!predicate()) {
    if (Date.now() > deadline) throw new Error('timed out waiting for language server')
    await new Promise(resolve => setTimeout(resolve, 10))
  }
}

function fixture(t) {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'infera-lsp-')))
  t.after(() => fs.rmSync(root, { recursive: true, force: true }))
  const file = path.join(root, 'main.nprolog')
  return { root, file, uri: pathToFileURL(file).href }
}

async function semanticTokens(request, uri) {
  const response = await request('textDocument/semanticTokens/full', { textDocument: { uri } })
  assert.ok(!response.error, JSON.stringify(response.error))
  let line = 0, col = 0
  const decoded = new Map()
  for (let i = 0; i < response.result.data.length; i += 5) {
    const [dl, dc, length, type, modifiers] = response.result.data.slice(i, i + 5)
    line += dl; col = dl === 0 ? col + dc : dc
    decoded.set(`${line}:${col}`, { length, type, modifiers })
  }
  return decoded
}

test('semantic tokens classify the Minesweeper CLP goals as operators, not comments', async t => {
  const { uri } = fixture(t)
  const text = fs.readFileSync(path.join(__dirname, '../../examples/minesweeper.nprolog'), 'utf8')
  const { notify, request } = await client(t, '/missing-infera', { checkOnSave: false, checkOnChange: false })
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text } })
  const response = await request('textDocument/semanticTokens/full', { textDocument: { uri } })
  assert.ok(!response.error, JSON.stringify(response.error))
  const { TOKEN_TYPES, tokenize } = require('../server/analysis')
  let line = 0, col = 0
  const decoded = new Map()
  for (let i = 0; i < response.result.data.length; i += 5) {
    const [dl, dc, length, type] = response.result.data.slice(i, i + 5)
    line += dl; col = dl === 0 ? col + dc : dc
    decoded.set(`${line}:${col}`, { length, type: TOKEN_TYPES[type] })
  }
  for (const token of tokenize(text)) {
    if (token.type === 'op' && token.text.startsWith('#')) {
      assert.deepEqual(decoded.get(`${token.line}:${token.col}`), { length: token.text.length, type: 'operator' }, token.text)
    } else if (token.type === 'comment') {
      assert.equal(decoded.get(`${token.line}:${token.col}`).type, 'comment')
    }
  }
})

test('unsafe and dynamic semantic tokens resolve imports and update from open buffers and module maps', async t => {
  const { root, uri } = fixture(t)
  const { analyzeDocument, TM } = require('../server/analysis')
  const lib = path.join(root, 'lib.nprolog'), libUri = pathToFileURL(lib).href
  const other = path.join(root, 'other.nprolog')
  const conf = path.join(root, 'neoprolog.conf')
  fs.writeFileSync(lib, 'p : unsafe dynamic (int: <=).\np 1.\np 1 2.\n')
  fs.writeFileSync(other, 'p 1.\n')
  fs.writeFileSync(conf, `lib#test ${lib}\n`)
  const text = '<- import "lib#test".\np X.\nmain <- p 1, lib:p 1, lib:p 1 2, wrapper p, write "p".\n'
  const { notify, request } = await client(t, '/missing-infera', { checkOnSave: false, checkOnChange: false }, root)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text } })
  const a = analyzeDocument(text), refs = a.qualifiedRefs.get('lib')
  const get = async () => {
    const decoded = await semanticTokens(request, uri)
    return refs.map(r => decoded.get(`${r.predLoc.line}:${r.predLoc.col}`).modifiers)
  }
  assert.deepEqual(await get(), [TM.unsafe | TM.dynamic, 0])
  const decoded = await semanticTokens(request, uri)
  for (const r of a.predicateRefs.get('p')) assert.equal(decoded.get(`${r.line}:${r.col}`).modifiers, 0)
  notify('textDocument/didOpen', { textDocument: { uri: libUri, languageId: 'infera', version: 1, text: 'p 1.\n' } })
  assert.deepEqual(await get(), [0, 0], 'unsaved imports supersede disk metadata')
  notify('textDocument/didChange', { textDocument: { uri: libUri, version: 2 }, contentChanges: [{ text: 'p : dynamic.\np 1.\np 1 2.\n' }] })
  assert.deepEqual(await get(), [TM.dynamic, TM.dynamic])
  notify('textDocument/didClose', { textDocument: { uri: libUri } })
  assert.deepEqual(await get(), [TM.unsafe | TM.dynamic, 0], 'closing restores disk declarations')
  fs.writeFileSync(lib, 'p : unsafe.\np 1.\np 1 2.\n')
  notify('workspace/didChangeWatchedFiles', { changes: [{ uri: libUri, type: 2 }] })
  assert.deepEqual(await get(), [TM.unsafe, TM.unsafe], 'file changes invalidate imported metadata')
  fs.writeFileSync(conf, `lib#test ${other}\n`)
  notify('workspace/didChangeWatchedFiles', { changes: [{ uri: pathToFileURL(conf).href, type: 2 }] })
  assert.deepEqual(await get(), [0, 0], 'changed module mappings clear old flags')
  fs.writeFileSync(conf, `lib#test ${lib}\n`)
  notify('workspace/didChangeWatchedFiles', { changes: [{ uri: pathToFileURL(conf).href, type: 2 }] })
  assert.deepEqual(await get(), [TM.unsafe, TM.unsafe])
  notify('textDocument/didChange', { textDocument: { uri, version: 2 }, contentChanges: [{ text: text.replace('<- import "lib#test".', '# import removed') }] })
  assert.deepEqual(await get(), [0, 0], 'removing an import clears its flags')
})

test('nl hover distinguishes the pure DCG helper from the newline effect', async t => {
  const { uri } = fixture(t)
  const lines = ['main <- nl.', 'grid [Row | Rows] -> grid_row Row, nl, grid Rows.',
    'escaped -> { nl }.', '> phrase nl Text?']
  const { notify, request } = await client(t, '/missing-infera', { checkOnSave: false, checkOnChange: false })
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: lines.join('\n') } })
  for (const [line, source] of lines.entries()) {
    const result = await request('textDocument/hover', { textDocument: { uri }, position: { line, character: source.indexOf('nl') } })
    const doc = result.result.contents.value
    if (line === 1 || line === 3) {
      assert.match(doc, /DCG helper/)
      assert.match(doc, /pure/)
      assert.match(doc, /does not need `unsafe`/)
    } else {
      assert.match(doc, /writes a newline/)
      assert.match(doc, /must be declared `unsafe`/)
    }
  }
})

test('flags-only declarations have name-wide document symbols without a null arity', async t => {
  const { uri } = fixture(t)
  const text = 'best_so_far : dynamic.\nwalk : notable.\nwalk 1.\ntyped : det (int: <=).\ntyped 1.\n'
  const { notify, request } = await client(t, '/missing-infera', { checkOnSave: false, checkOnChange: false })
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text } })
  const response = await request('textDocument/documentSymbol', { textDocument: { uri } })
  assert.deepEqual(response.result.map(symbol => symbol.name), [
    'best_so_far (declaration)', 'walk (declaration)', 'typed/1 (declaration)', 'walk/1', 'typed/1'
  ])
})

test('CLP comparisons, control operators and declaration modes expose their hover docs', async t => {
  const { uri } = fixture(t)
  const lines = ['p : (int: <=) (int: =>) (any: <=>).',
    'p X Y Z <- X #= Y, X #!= Z, X #< Y, X #> Z, X #<= Y, X #>= Z, (true -> ! ; fail).']
  const { notify, request } = await client(t, '/missing-infera', { checkOnSave: false, checkOnChange: false })
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: lines.join('\n') } })
  for (const [line, operator, expected] of [
    [0, '<=', 'Input mode'], [0, '=>', 'Output mode'], [0, '<=>', 'In/out mode'],
    ...['#=', '#!=', '#<', '#>', '#<=', '#>='].map(op => [1, op, 'CLP(Z)']),
    [1, '->', 'if-then-else'], [1, '!', 'cut'], [1, ';', 'disjunction']
  ]) {
    const response = await request('textDocument/hover', { textDocument: { uri },
      position: { line, character: operator === '!' ? lines[line].lastIndexOf(operator) : lines[line].indexOf(operator) } })
    assert.ok(response.result, operator)
    assert.ok(response.result.contents.value.includes(expected), `${operator}: ${response.result.contents.value}`)
  }
})

test('CLP hover includes propagation examples across the complete operator range', async t => {
  const { uri } = fixture(t)
  const operators = ['#=', '#!=', '#<', '#>', '#<=', '#>=']
  const lines = operators.map(op => `p X Y <- X ${op} Y.`)
  const { notify, request } = await client(t, '/missing-infera', { checkOnSave: false, checkOnChange: false })
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: lines.join('\n') } })
  for (const [line, op] of operators.entries()) {
    const start = lines[line].indexOf(op)
    for (let offset = 0; offset < op.length; offset++) {
      const response = await request('textDocument/hover', { textDocument: { uri }, position: { line, character: start + offset } })
      assert.ok(response.result.contents.value.includes('Example:'), op)
      assert.deepEqual(response.result.range, { start: { line, character: start }, end: { line, character: start + op.length } })
      if (op === '#=') assert.match(response.result.contents.value, /Unlike `is`/)
    }
  }
})

function countingChecker(root, diagnostics = [], markSnapshots = false) {
  const executable = path.join(root, 'counting-checker'), log = path.join(root, 'checks.jsonl')
  fs.writeFileSync(executable, '#!/usr/bin/env node\n'
    + `const fs = require('fs'), args = process.argv.slice(2); let source = '';\n`
    + `process.stdin.on('data', chunk => { source += chunk });\n`
    + `process.stdin.on('end', () => {\n`
    + `const buffers = []; for (let i = 4; i < args.length; i += 3) buffers.push({ path: args[i+1], text: fs.readFileSync(args[i+2], 'utf8') });\n`
    + `fs.appendFileSync(${JSON.stringify(log)}, JSON.stringify({ file: args[3], source, buffers }) + '\\n');\n`
    + `const diagnostics = ${JSON.stringify(diagnostics)};\n`
    + `if (${JSON.stringify(markSnapshots)}) for (const diagnostic of diagnostics) { diagnostic.file = args[3]; diagnostic.message += '\\n' + JSON.stringify({ source, buffers }); }\n`
    + `console.log(JSON.stringify(diagnostics)); });\n`, { mode: 0o755 })
  const calls = file => {
    const rows = fs.existsSync(log) ? fs.readFileSync(log, 'utf8').trim().split('\n').filter(Boolean).map(JSON.parse) : []
    return file ? rows.filter(row => row.file === file) : rows
  }
  return { executable, calls }
}

test('unchanged content saves and watcher events reuse checks; edits leave unrelated files alone', async t => {
  const { root, file, uri } = fixture(t)
  const other = path.join(root, 'other.nprolog'), otherUri = pathToFileURL(other).href
  const { executable, calls } = countingChecker(root)
  const { notify } = await client(t, executable)
  for (const [f, u, text] of [[file, uri, 'main.\n'], [other, otherUri, 'other.\n']]) {
    fs.writeFileSync(f, text)
    notify('textDocument/didOpen', { textDocument: { uri: u, languageId: 'infera', version: 1, text } })
  }
  await until(() => calls(file).length === 1 && calls(other).length === 1)
  for (let i = 0; i < 3; i++) notify('textDocument/didSave', { textDocument: { uri } })
  notify('textDocument/didChange', { textDocument: { uri, version: 2 }, contentChanges: [{ text: 'main.\n' }] })
  notify('workspace/didChangeWatchedFiles', { changes: [{ uri, type: 2 }, { uri: otherUri, type: 2 }] })
  await new Promise(resolve => setTimeout(resolve, 500))
  assert.equal(calls(file).length, 1)
  assert.equal(calls(other).length, 1)
  notify('textDocument/didChange', { textDocument: { uri, version: 3 }, contentChanges: [{ text: 'changed.\n' }] })
  notify('textDocument/didSave', { textDocument: { uri } })
  await until(() => calls(file).length === 2)
  await new Promise(resolve => setTimeout(resolve, 300))
  assert.equal(calls(file).length, 2)
  assert.equal(calls(other).length, 1)
})

test('only transitive importers recheck and receive relevant unsaved snapshots', async t => {
  const { root, file, uri } = fixture(t)
  const lib = path.join(root, 'lib.nprolog'), leaf = path.join(root, 'leaf.nprolog')
  const leafUri = pathToFileURL(leaf).href, other = path.join(root, 'other.nprolog'), otherUri = pathToFileURL(other).href
  fs.writeFileSync(path.join(root, 'neoprolog.conf'), 'lib#test lib.nprolog\nleaf#test leaf.nprolog\n')
  fs.writeFileSync(lib, '<- import "leaf#test".\nlib.\n')
  fs.writeFileSync(leaf, 'leaf.\n')
  const completed = { file, code: 'test-importer-check-completed', severity: 'warning', message: 'checked snapshot',
    range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } }
  const { executable, calls } = countingChecker(root, [completed], true)
  const { notify, messages } = await client(t, executable)
  // The checker logs before the server caches its result. Await the warning
  // for this exact snapshot so an earlier cached publication cannot unblock us.
  const published = (marker, checkedFile, checkedUri) => {
    const checked = calls(checkedFile).at(-1)
    if (!checked) return false
    const message = completed.message + '\n' + JSON.stringify({ source: checked.source, buffers: checked.buffers })
    return messages.slice(marker).some(m => m.method === 'textDocument/publishDiagnostics' && m.params.uri === checkedUri
      && m.params.diagnostics.some(d => d.code === completed.code && d.message === message))
  }
  for (const [f, u, text] of [[file, uri, '<- import "lib#test".\nmain.\n'], [other, otherUri, 'other.\n'], [leaf, leafUri, 'leaf.\n']]) {
    fs.writeFileSync(f, text)
    notify('textDocument/didOpen', { textDocument: { uri: u, languageId: 'infera', version: 1, text } })
  }
  await until(() => calls(file).length === 1 && calls(leaf).length === 1 && calls(other).length === 1
    && published(0, file, uri) && published(0, leaf, leafUri) && published(0, other, otherUri))
  const changedAt = messages.length
  notify('textDocument/didChange', { textDocument: { uri: leafUri, version: 2 }, contentChanges: [{ text: 'unsaved.\n' }] })
  await until(() => calls(file).length === 2 && calls(leaf).length === 2
    && published(changedAt, file, uri) && published(changedAt, leaf, leafUri))
  assert.deepEqual(calls(file).at(-1).buffers, [{ path: leaf, text: 'unsaved.\n' }])
  assert.equal(calls(other).length, 1)
  const closedAt = messages.length
  notify('textDocument/didClose', { textDocument: { uri: leafUri } })
  await until(() => calls(file).length === 3 && published(closedAt, file, uri))
  assert.equal(calls(file).length, 3)
  assert.deepEqual(calls(file).at(-1).buffers, [])
  assert.equal(calls(other).length, 1)
})

test('missing disk imports and configuration changes invalidate cached checks', async t => {
  const { root, file, uri } = fixture(t)
  const lib = path.join(root, 'lib.nprolog'), libUri = pathToFileURL(lib).href
  const conf = path.join(root, 'neoprolog.conf'), confUri = pathToFileURL(conf).href
  fs.writeFileSync(conf, 'lib#test lib.nprolog\n')
  // Start with the import present: a check whose inputs match an earlier
  // snapshot may legitimately reuse that cached result, so the missing-file
  // snapshot below must be new to the server rather than a return to the first.
  fs.writeFileSync(lib, 'lib0.\n')
  const { executable, calls } = countingChecker(root), { notify } = await client(t, executable)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: '<- import "lib#test".\nmain.\n' } })
  await until(() => calls(file).length === 1)
  fs.writeFileSync(lib, 'lib.\n')
  notify('workspace/didChangeWatchedFiles', { changes: [{ uri: libUri, type: 2 }] })
  await until(() => calls(file).length === 2)
  fs.unlinkSync(lib)
  notify('workspace/didChangeWatchedFiles', { changes: [{ uri: libUri, type: 3 }] })
  await until(() => calls(file).length === 3)
  fs.writeFileSync(conf, 'lib#test elsewhere.nprolog\n')
  notify('workspace/didChangeWatchedFiles', { changes: [{ uri: confUri, type: 2 }] })
  await until(() => calls(file).length === 4)
})

test('hint visibility reuses unfiltered diagnostics while compiler changes invalidate the cache', async t => {
  const { root, file, uri } = fixture(t)
  const row = { file, code: 'perf-example', severity: 'information', message: 'hint',
    range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } }
  const { executable, calls } = countingChecker(root, [row])
  const { notify, messages } = await client(t, executable)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: 'main.\n' } })
  const last = () => messages.filter(m => m.method === 'textDocument/publishDiagnostics' && m.params.uri === uri).at(-1)?.params.diagnostics
  await until(() => last()?.some(d => d.code === row.code))
  notify('workspace/didChangeConfiguration', { settings: { infera: { executable, performanceHints: false } } })
  await until(() => last()?.length === 0)
  notify('workspace/didChangeConfiguration', { settings: { infera: { executable, performanceHints: true } } })
  await until(() => last()?.some(d => d.code === row.code))
  assert.equal(calls(file).length, 1)
  fs.utimesSync(executable, new Date(), new Date(Date.now() + 10000))
  notify('textDocument/didSave', { textDocument: { uri } })
  await until(() => calls(file).length === 2)
})

test('save-only checks still run after an edit queued with live checking disabled', async t => {
  const { root, file, uri } = fixture(t)
  const { executable, calls } = countingChecker(root), { notify } = await client(t, executable, { checkOnChange: false })
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: 'main.\n' } })
  await until(() => calls(file).length === 1)
  notify('textDocument/didChange', { textDocument: { uri, version: 2 }, contentChanges: [{ text: 'changed.\n' }] })
  notify('textDocument/didSave', { textDocument: { uri } })
  await until(() => calls(file).length === 2)
})

test('an in-flight importer cannot publish results for an older dependency buffer', async t => {
  const { root, file, uri } = fixture(t)
  const lib = path.join(root, 'lib.nprolog'), libUri = pathToFileURL(lib).href
  fs.writeFileSync(lib, 'old.\n')
  fs.writeFileSync(path.join(root, 'neoprolog.conf'), 'lib#test lib.nprolog\n')
  const executable = path.join(root, 'delayed-import-checker'), marker = path.join(root, 'importer-started')
  const row = { file, code: 'stale-dependency', severity: 'warning', message: 'old dependency',
    range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } }
  fs.writeFileSync(executable, '#!/usr/bin/env node\n'
    + `const fs = require('fs'), args = process.argv.slice(2); process.stdin.resume();\n`
    + `process.stdin.on('end', () => { if (args[3] !== ${JSON.stringify(file)}) { console.log('[]'); return }\n`
    + `let text = fs.readFileSync(${JSON.stringify(lib)}, 'utf8');\n`
    + `for (let i = 4; i < args.length; i += 3) if (args[i+1] === ${JSON.stringify(lib)}) text = fs.readFileSync(args[i+2], 'utf8');\n`
    + `fs.writeFileSync(${JSON.stringify(marker)}, text);\n`
    + `if (text.includes('old')) setTimeout(() => console.log(${JSON.stringify(JSON.stringify([row]))}), 600); else console.log('[]'); });\n`, { mode: 0o755 })
  const { notify, messages } = await client(t, executable)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: '<- import "lib#test".\nmain.\n' } })
  notify('textDocument/didOpen', { textDocument: { uri: libUri, languageId: 'infera', version: 1, text: 'old.\n' } })
  await until(() => fs.existsSync(marker))
  const from = messages.length
  notify('textDocument/didChange', { textDocument: { uri: libUri, version: 2 }, contentChanges: [{ text: 'new.\n' }] })
  await until(() => fs.readFileSync(marker, 'utf8') === 'new.\n')
  await new Promise(resolve => setTimeout(resolve, 800))
  assert.ok(!messages.slice(from).some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.some(d => d.code === row.code)))
})

test('checker failures are retried on an unchanged save', async t => {
  const { root, file, uri } = fixture(t)
  const executable = path.join(root, 'recovering-checker'), recovered = path.join(root, 'recovered')
  fs.writeFileSync(executable, '#!/usr/bin/env node\n'
    + `process.stdin.resume(); process.stdin.on('end', () => {\n`
    + `if (require('fs').existsSync(${JSON.stringify(recovered)})) console.log('[]'); else process.exit(1); });\n`, { mode: 0o755 })
  const { notify, messages } = await client(t, executable)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: 'main.\n' } })
  await until(() => messages.some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.some(d => d.code === 'checker-unavailable')))
  const from = messages.length
  fs.writeFileSync(recovered, '')
  notify('textDocument/didSave', { textDocument: { uri } })
  await until(() => messages.slice(from).some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.length === 0))
})

test('nested module navigation uses the same nearest config and relative paths as checking', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const { root } = fixture(t)
  const wrong = path.join(root, 'wrong'), project = path.join(root, 'project'), nested = path.join(project, 'nested')
  fs.mkdirSync(wrong); fs.mkdirSync(nested, { recursive: true })
  fs.writeFileSync(path.join(wrong, 'lib.nprolog'), 'wrong.\n')
  fs.writeFileSync(path.join(wrong, 'neoprolog.conf'), 'lib#test lib.nprolog\n')
  fs.writeFileSync(path.join(project, 'lib.nprolog'), 'also_wrong.\n')
  fs.writeFileSync(path.join(project, 'neoprolog.conf'), 'lib#test lib.nprolog\n')
  const lib = path.join(nested, 'lib.nprolog')
  fs.writeFileSync(lib, 'greet.\n')
  fs.writeFileSync(path.join(nested, 'infera.conf'), 'lib#test\tlib.nprolog\n')
  const file = path.join(nested, 'main.nprolog'), uri = pathToFileURL(file).href
  const text = '<- import "lib#test".\nmain <- lib:greet.\n'
  const { notify, request, messages } = await client(t, process.env.INFERA_BIN, {}, [wrong, project])
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text } })
  await until(() => messages.filter(m => m.method === 'textDocument/publishDiagnostics' && m.params.uri === uri).length >= 2)
  assert.deepEqual(messages.filter(m => m.method === 'textDocument/publishDiagnostics' && m.params.uri === uri).at(-1).params.diagnostics, [])
  const definition = await request('textDocument/definition', { textDocument: { uri }, position: { line: 1, character: 14 } })
  assert.equal(definition.result[0].uri, pathToFileURL(lib).href)
  const completion = await request('textDocument/completion', { textDocument: { uri }, position: { line: 1, character: 12 } })
  assert.deepEqual(completion.result.map(item => item.label), ['greet'])
})

test('performance hints can be toggled without suppressing correctness diagnostics', async t => {
  const { root, file, uri } = fixture(t)
  const executable = path.join(root, 'checker')
  const range = { start: { line: 0, character: 0 }, end: { line: 0, character: 4 } }
  const rows = [
    { file, range, code: 'perf-non-tail-recursion', severity: 'information', message: 'Move remaining work before this call when possible.' },
    { file, range, code: 'perf-label-early', severity: 'hint', message: 'Post constraints before labeling.' },
    { file, range, code: 'singleton-variable', severity: 'warning', message: 'Singleton X' },
    { file, range, code: 'undefined-predicate', severity: 'error', message: 'Missing predicate' }
  ]
  fs.writeFileSync(executable, '#!/usr/bin/env node\n'
    + `process.stdin.resume(); process.stdin.on('end', () => { console.log(${JSON.stringify(JSON.stringify(rows))}); process.exit(1) });\n`, { mode: 0o755 })
  const { notify, messages } = await client(t, executable)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: 'main <- missing.\n' } })
  const completed = from => messages.slice(from).filter(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.some(d => d.code === 'undefined-predicate')).at(-1)?.params.diagnostics
  await until(() => completed(0)?.length === 4)
  assert.deepEqual(completed(0).map(d => d.severity), [3, 4, 2, 1])
  const from = messages.length
  notify('workspace/didChangeConfiguration', { settings: { infera: { executable, performanceHints: false } } })
  await until(() => completed(from)?.length === 2)
  assert.deepEqual(completed(from).map(d => d.code), ['singleton-variable', 'undefined-predicate'])
  const back = messages.length
  notify('workspace/didChangeConfiguration', { settings: { infera: { executable, performanceHints: true } } })
  await until(() => completed(back)?.length === 4)
})

test('real compiler performance suggestions have exact identifier ranges and follow edits and settings', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const { root, file, uri } = fixture(t)
  const source = 'p "😀" X Y <- p "😀" X Z, Y = Z.\n'
  const check = spawnSync(process.env.INFERA_BIN, ['check', '--json', '--stdin', file],
    { cwd: root, input: source, encoding: 'utf8' })
  assert.equal(check.status, 0, check.stderr)
  const expected = compilerDiagnostics(check.stdout, file)
    .find(d => d.code === 'perf-non-tail-recursion')
  assert.ok(expected, check.stdout)
  assert.equal(expected.severity, 3)
  const start = source.indexOf('p', 1) // String offsets and LSP columns use UTF-16.
  assert.deepEqual(expected.range, {
    start: { line: 0, character: start }, end: { line: 0, character: start + 1 }
  })
  const { notify, messages } = await client(t, process.env.INFERA_BIN)
  const published = from => messages.slice(from).filter(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri).at(-1)?.params.diagnostics
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: source } })
  await until(() => published(0)?.some(d => d.code === 'perf-non-tail-recursion'))
  assert.deepEqual(published(0).find(d => d.code === 'perf-non-tail-recursion'), expected)

  let from = messages.length
  notify('workspace/didChangeConfiguration', { settings: { infera: {
    executable: process.env.INFERA_BIN, performanceHints: false
  } } })
  await until(() => messages.slice(from).filter(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri).length >= 2)
  assert.deepEqual(published(from), [], 'valid source remains valid when suggestions are hidden')

  from = messages.length
  notify('textDocument/didChange', { textDocument: { uri, version: 2 }, contentChanges: [{ text: source + 'main <- missing.\n' }] })
  await until(() => published(from)?.some(d => d.code === 'undefined-predicate'))
  assert.ok(published(from).every(d => !String(d.code).startsWith('perf-')))
  from = messages.length
  notify('workspace/didChangeConfiguration', { settings: { infera: {
    executable: process.env.INFERA_BIN, performanceHints: true
  } } })
  await until(() => published(from)?.some(d => d.code === 'perf-non-tail-recursion'))
  assert.ok(published(from).some(d => d.code === 'undefined-predicate'))

  from = messages.length
  const tail = 'p "😀" X Y <- X = Y, p "😀" X Y.\nmain <- missing.\n'
  notify('textDocument/didChange', { textDocument: { uri, version: 3 }, contentChanges: [{ text: tail }] })
  await until(() => published(from)?.some(d => d.code === 'undefined-predicate'))
  assert.ok(published(from).every(d => d.code !== 'perf-non-tail-recursion'),
    'a checked live edit clears the obsolete suggestion while retaining errors')
  assert.equal(fs.existsSync(file), false, 'checks do not save the source buffer')
})

test('real compiler diagnostics arrive on open and clear after a saved correction', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const { file, uri } = fixture(t)
  const text = 'main <- missing.\n'
  fs.writeFileSync(file, text)
  const { notify, messages } = await client(t, process.env.INFERA_BIN)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text } })
  await until(() => messages.some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.some(d => d.code === 'undefined-predicate')))
  const corrected = 'main.\n'
  fs.writeFileSync(file, corrected)
  const from = messages.length
  notify('textDocument/didChange', { textDocument: { uri, version: 2 }, contentChanges: [{ text: corrected }] })
  notify('textDocument/didSave', { textDocument: { uri } })
  await until(() => messages.slice(from).some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.length === 0))
  const wrongArity = 'p 1.\nmain <- p.\n'
  fs.writeFileSync(file, wrongArity)
  const savedFrom = messages.length
  notify('textDocument/didChange', { textDocument: { uri, version: 3 }, contentChanges: [{ text: wrongArity }] })
  notify('textDocument/didSave', { textDocument: { uri } })
  await until(() => messages.slice(savedFrom).some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.some(d => d.code === 'wrong-arity')))
})

test('a delayed compiler result cannot overwrite an edited document', { timeout: 20000 }, async t => {
  const { root, file, uri } = fixture(t)
  fs.writeFileSync(file, 'main.\n')
  const executable = path.join(root, 'delayed-checker')
  const marker = path.join(root, 'started')
  const row = { file, code: 'delayed', severity: 'error', message: 'stale',
    range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } }
  fs.writeFileSync(executable, '#!/usr/bin/env node\n'
    + `require('fs').writeFileSync(${JSON.stringify(marker)}, 'started');\n`
    + `setTimeout(() => { console.log(${JSON.stringify(JSON.stringify([row]))}); process.exit(1) }, 300);\n`, { mode: 0o755 })
  const { notify, messages } = await client(t, executable, { checkOnChange: false })
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: 'main.\n' } })
  await until(() => fs.existsSync(marker))
  const from = messages.length
  notify('textDocument/didChange', { textDocument: { uri, version: 2 }, contentChanges: [{ text: 'corrected.\n' }] })
  await new Promise(resolve => setTimeout(resolve, 500))
  assert.ok(!messages.slice(from).some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.diagnostics.some(d => d.code === 'delayed')))
})

test('unsaved editor diagnostics exactly match the compiler across a validation corpus', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const { file, uri, root } = fixture(t)
  fs.writeFileSync(file, 'disk_only.\n')
  const { notify, messages } = await client(t, process.env.INFERA_BIN)
  const corpus = [
    'main <- missing.\n',
    'p 1.\nmain <- p.\n',
    'p X.\n',
    'p : det (int: <=).\np 1.\n> p "bad"?\n',
    'p : det semidet.\n',
    'lonely : semidet (str: <=).\n',
    '<- frobnicate.\n',
    'last X',
    'p "😀".\tbad <- missing.\n',
    'p 1.\n> p [1, ?\n',
    'p : det (int: <=).\np 2.\n> p (1 + 1)?\n',
    { text: '> nl?\n', status: 0 },
    { text: 'main : unsafe.\nmain <- nl.\n', status: 0 },
    { text: 'main <- nl.\n', status: 1, errorCode: 'unsafe-call' },
    { text: 'escaped -> { nl }.\n', status: 1, errorCode: 'unsafe-call' },
    { text: 'grid [] -> [].\ngrid [Row | Rows] -> grid_row Row, nl, grid Rows.\ngrid_row Row -> seq Row.\n', status: 0 },
    { text: 'best_so_far : dynamic.\n', status: 0 },
    { text: 'best_so_far : dynamic.\nrecord : unsafe.\nrecord <- assert (best_so_far 1), retractall (best_so_far _).\n', status: 0 },
    { text: 'puzzle X Y Truth <- [X, Y] in 0..9, all_different [X, Y], reify (X #<= Y) Truth, Cost #= X + Y, labeling [min Cost] [X, Y].\n', status: 0 },
    { text: 'pick 1.\npick 2.\nrun Ys <- once (pick X), not (X = 3), findall Y (pick Y) Ys, (X = 1 -> true ; fail), forall (pick Z) (Z > 0), call pick X, minimize Best (pick Best).\n', status: 0 }
  ]
  for (const [i, entry] of corpus.entries()) {
    const { text, status, errorCode } = typeof entry === 'string' ? { text: entry } : entry
    const version = i + 1
    const result = spawnSync(process.env.INFERA_BIN, ['check', '--json', '--stdin', file],
      { cwd: root, input: text, encoding: 'utf8' })
    assert.ok([0, 1].includes(result.status), result.stderr)
    const expected = compilerDiagnostics(result.stdout, file)
    if (status !== undefined) assert.equal(result.status, status, `${text}\n${result.stdout}\n${result.stderr}`)
    if (errorCode) assert.ok(expected.some(d => d.severity === 1 && d.code === errorCode), result.stdout)
    if (i === 0) notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version, text } })
    else notify('textDocument/didChange', { textDocument: { uri, version }, contentChanges: [{ text }] })
    await until(() => {
      const published = messages.filter(m => m.method === 'textDocument/publishDiagnostics'
        && m.params.uri === uri && m.params.version === version)
      return published.length >= 2 && JSON.stringify(published.at(-1).params.diagnostics) === JSON.stringify(expected)
    })
  }
  assert.equal(fs.readFileSync(file, 'utf8'), 'disk_only.\n', 'editor checks must not save the buffer')
})

test('shipped Minesweeper, IO and registered facts examples have current compiler diagnostics in the editor', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const repository = path.resolve(__dirname, '../..')
  const { root } = fixture(t)
  fs.mkdirSync(path.join(root, 'examples'))
  fs.copyFileSync(path.join(repository, 'infera.conf'), path.join(root, 'infera.conf'))
  for (const name of ['minesweeper', 'io', 'facts', 'facts2']) {
    fs.copyFileSync(path.join(repository, 'examples', `${name}.nprolog`), path.join(root, 'examples', `${name}.nprolog`))
  }
  // A developer's ignored examples/neoprolog.conf may contain different
  // registrations. Exercise the tracked example map in a clean checkout.
  const { notify, request, messages } = await client(t, process.env.INFERA_BIN, {}, root)
  for (const name of ['minesweeper', 'io', 'facts2']) {
    const file = path.join(root, 'examples', `${name}.nprolog`), uri = pathToFileURL(file).href
    const text = fs.readFileSync(file, 'utf8')
    const checked = spawnSync(process.env.INFERA_BIN, ['check', '--json', '--stdin', file],
      { cwd: root, input: text, encoding: 'utf8' })
    assert.equal(checked.status, 0, `${name}: ${checked.stdout}\n${checked.stderr}`)
    const expected = compilerDiagnostics(checked.stdout, file)
    assert.ok(expected.every(d => d.severity !== 1), `${name}: ${checked.stdout}`)
    const from = messages.length
    notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text } })
    try {
      await until(() => {
        const published = messages.slice(from).filter(m => m.method === 'textDocument/publishDiagnostics' && m.params.uri === uri)
        return published.length >= 2 && JSON.stringify(published.at(-1).params.diagnostics) === JSON.stringify(expected)
      })
    } catch (failure) {
      assert.fail(`${name}: ${failure.message}\nExpected: ${JSON.stringify(expected)}\nMessages: ${JSON.stringify(messages.slice(from))}`)
    }
    if (name === 'facts2') {
      const lines = text.split('\n'), line = lines.findIndex(source => source.includes('facts:factorial'))
      const definition = await request('textDocument/definition', { textDocument: { uri },
        position: { line, character: lines[line].indexOf('factorial') } })
      assert.equal(definition.result[0].uri, pathToFileURL(path.join(root, 'examples/facts.nprolog')).href)
    }
    notify('textDocument/didClose', { textDocument: { uri } })
  }
})

test('an unregistered facts key remains a compiler error even when the module file exists', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const { root, file, uri } = fixture(t)
  fs.writeFileSync(path.join(root, 'facts.nprolog'), 'factorial 0 1.\n')
  fs.writeFileSync(path.join(root, 'infera.conf'), 'facts#current facts.nprolog\n')
  const text = '<- import "facts#stale".\n> facts:factorial 0 R?\n'
  const checked = spawnSync(process.env.INFERA_BIN, ['check', '--json', '--stdin', file],
    { cwd: root, input: text, encoding: 'utf8' })
  assert.equal(checked.status, 1)
  const expected = compilerDiagnostics(checked.stdout, file)
  assert.equal(expected[0].code, 'load-error')
  assert.match(expected[0].message, /facts#stale/)
  const { notify, messages } = await client(t, process.env.INFERA_BIN, {}, root)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text } })
  await until(() => messages.filter(m => m.method === 'textDocument/publishDiagnostics' && m.params.uri === uri)
    .some(m => JSON.stringify(m.params.diagnostics) === JSON.stringify(expected)))
})

test('unsaved imports update diagnostics in every affected open buffer', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const { root, file, uri } = fixture(t)
  const lib = path.join(root, 'lib.nprolog'), libUri = pathToFileURL(lib).href
  fs.writeFileSync(lib, 'greet.\n')
  fs.writeFileSync(path.join(root, 'neoprolog.conf'), `lib#test ${lib}\n`)
  const text = '<- import "lib#test".\nmain <- lib:greet.\n'
  fs.writeFileSync(file, text)
  const { notify, messages } = await client(t, process.env.INFERA_BIN)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text } })
  const from = messages.length
  notify('textDocument/didOpen', { textDocument: { uri: libUri, languageId: 'infera', version: 1, text: 'greet <- missing.\n' } })
  await until(() => messages.slice(from).some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.some(d => d.code === 'undefined-predicate'
      && d.relatedInformation?.[0].location.uri === libUri)))
  const correctedFrom = messages.length
  notify('textDocument/didChange', { textDocument: { uri: libUri, version: 2 }, contentChanges: [{ text: 'greet.\n' }] })
  await until(() => messages.slice(correctedFrom).filter(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.length === 0).length >= 2)
  assert.equal(fs.readFileSync(lib, 'utf8'), 'greet.\n')
})

test('missing compiler is reported explicitly without JavaScript validation', { timeout: 20000 }, async t => {
  const { root, file, uri } = fixture(t)
  fs.writeFileSync(file, 'main <- missing.\n')
  const { notify, messages } = await client(t, path.join(root, 'no-compiler'))
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: 'main <- missing.\n' } })
  await until(() => messages.some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.some(d => d.code === 'checker-unavailable')))
  assert.ok(!messages.some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.diagnostics.some(d => d.message.includes('undefined predicate'))))
})

test('untitled buffers are checked without creating a source file', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const { root } = fixture(t)
  const uri = 'untitled:Untitled-1'
  const { notify, messages } = await client(t, process.env.INFERA_BIN, {}, root)
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: 'main <- missing.\n' } })
  await until(() => messages.some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.diagnostics.some(d => d.code === 'undefined-predicate' && !d.relatedInformation)))
  assert.deepEqual(fs.readdirSync(root), [])
})

test('disabled save checks preserve live checks during autosave, and both settings disable validation', {
  skip: !process.env.INFERA_BIN, timeout: 20000
}, async t => {
  const { file, uri } = fixture(t)
  fs.writeFileSync(file, 'disk.\n')
  const { notify, messages } = await client(t, process.env.INFERA_BIN, { checkOnSave: false, checkOnChange: true })
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'infera', version: 1, text: 'main <- missing.\n' } })
  notify('textDocument/didSave', { textDocument: { uri } })
  await until(() => messages.some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.version === 1 && m.params.diagnostics.some(d => d.code === 'undefined-predicate')))
  notify('textDocument/didChange', { textDocument: { uri, version: 2 }, contentChanges: [{ text: 'p 1.\nmain <- p.\n' }] })
  notify('textDocument/didSave', { textDocument: { uri } })
  await until(() => messages.some(m => m.method === 'textDocument/publishDiagnostics'
    && m.params.uri === uri && m.params.version === 2 && m.params.diagnostics.some(d => d.code === 'wrong-arity')))
  const from = messages.length
  notify('workspace/didChangeConfiguration', { settings: { infera: {
    executable: process.env.INFERA_BIN, checkOnSave: false, checkOnChange: false
  } } })
  notify('textDocument/didChange', { textDocument: { uri, version: 3 }, contentChanges: [{ text: 'main <- missing.\n' }] })
  notify('textDocument/didSave', { textDocument: { uri } })
  await new Promise(resolve => setTimeout(resolve, 500))
  const published = messages.slice(from).filter(m => m.method === 'textDocument/publishDiagnostics' && m.params.uri === uri)
  assert.ok(published.length > 0 && published.every(m => m.params.diagnostics.length === 0))
})
