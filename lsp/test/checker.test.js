'use strict'
const test = require('node:test')
const assert = require('node:assert/strict')
const fs = require('fs')
const os = require('os')
const path = require('path')
const { compilerDiagnostics, visibleDiagnostics } = require('../server/checker')

const range = { start: { line: 2, character: 4 }, end: { line: 2, character: 12 } }
const row = { file: '/tmp/main.nprolog', severity: 'error', code: 'undefined-predicate', message: 'undefined predicate: missing/1', range }

test('compiler diagnostics preserve ranges, codes and severity', () => {
  const [d] = compilerDiagnostics(JSON.stringify([row]), row.file)
  assert.deepEqual(d.range, range)
  assert.equal(d.code, row.code)
  assert.equal(d.severity, 1)
  assert.equal(compilerDiagnostics(JSON.stringify([{ ...row, severity: 'warning' }]), row.file)[0].severity, 2)
  assert.equal(compilerDiagnostics(JSON.stringify([{ ...row, severity: 'information' }]), row.file)[0].severity, 3)
  assert.equal(compilerDiagnostics(JSON.stringify([{ ...row, severity: 'hint' }]), row.file)[0].severity, 4)
  assert.deepEqual(compilerDiagnostics('[]', row.file), [])
})

test('performance visibility only filters compiler performance suggestions', () => {
  const diagnostics = compilerDiagnostics(JSON.stringify([
    { ...row, severity: 'information', code: 'perf-non-tail-recursion' },
    { ...row, severity: 'warning', code: 'singleton-variable' },
    { ...row, severity: 'error', code: 'perf-future-error' }
  ]), row.file)
  assert.deepEqual(visibleDiagnostics(diagnostics, { performanceHints: false }), diagnostics.slice(1))
  assert.equal(visibleDiagnostics(diagnostics, { performanceHints: true }), diagnostics)
  assert.equal(visibleDiagnostics(diagnostics, {}), diagnostics)
})

test('import diagnostics link to the owning source file', () => {
  const [d] = compilerDiagnostics(JSON.stringify([row]), '/tmp/other.nprolog')
  assert.equal(d.range.start.line, 0)
  assert.equal(d.relatedInformation[0].location.uri, 'file:///tmp/main.nprolog')
  assert.deepEqual(d.relatedInformation[0].location.range, range)
})

test('invalid compiler output cannot silently become a successful check', () => {
  for (const output of ['ok', '{}', '[{}]', '[null]', JSON.stringify([{ ...row, range: {} }]),
    JSON.stringify([{ ...row, severity: 'verbose' }]),
    JSON.stringify([{ ...row, range: { start: { line: -1, character: 0 }, end: range.end } }])]) {
    assert.throws(() => compilerDiagnostics(output, row.file))
  }
})

test('canonical compiler paths match symlinked and not-yet-saved editor paths', t => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'infera-path-')))
  t.after(() => fs.rmSync(root, { recursive: true, force: true }))
  fs.mkdirSync(path.join(root, 'real'))
  fs.symlinkSync(path.join(root, 'real'), path.join(root, 'alias'), 'dir')
  const file = path.join(root, 'real', 'new.nprolog')
  const [d] = compilerDiagnostics(JSON.stringify([{ ...row, file }]), path.join(root, 'alias', 'new.nprolog'))
  assert.deepEqual(d.range, range)
  assert.equal(d.relatedInformation, undefined)
})
