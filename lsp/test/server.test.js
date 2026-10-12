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
    workspaceFolders: workspaceRoot ? [{ uri: pathToFileURL(workspaceRoot).href, name: 'test' }] : [] })
  notify('initialized', {})
  notify('workspace/didChangeConfiguration', { settings: { infera: { executable, checkOnSave: true, ...settings } } })
  return { notify, messages }
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
    'p : det (int: <=).\np 2.\n> p (1 + 1)?\n'
  ]
  for (const [i, text] of corpus.entries()) {
    const version = i + 1
    const result = spawnSync(process.env.INFERA_BIN, ['check', '--json', '--stdin', file],
      { cwd: root, input: text, encoding: 'utf8' })
    assert.ok([0, 1].includes(result.status), result.stderr)
    const expected = compilerDiagnostics(result.stdout, file)
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
