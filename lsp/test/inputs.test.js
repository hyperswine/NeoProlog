'use strict'

const test = require('node:test')
const assert = require('node:assert/strict')
const fs = require('fs')
const os = require('os')
const path = require('path')
const { checkerInputs, executableIdentity } = require('../server/inputs')

function fixture(t) {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'infera-inputs-')))
  t.after(() => fs.rmSync(root, { recursive: true, force: true }))
  const file = path.join(root, 'main.nprolog')
  const lib = path.join(root, 'lib.nprolog'), leaf = path.join(root, 'leaf.nprolog')
  fs.writeFileSync(path.join(root, 'neoprolog.conf'), 'lib#test lib.nprolog\nleaf#test leaf.nprolog\n')
  fs.writeFileSync(lib, '<- import "leaf#test".\nlib.\n')
  fs.writeFileSync(leaf, 'leaf.\n')
  return { root, file, lib, leaf, source: '<- import "lib#test".\nmain.\n' }
}

test('checker inputs follow transitive imports and exclude unrelated buffers', t => {
  const { file, lib, leaf, source, root } = fixture(t)
  const inputs = checkerInputs(file, source, [{ path: leaf, text: 'changed.\n' },
    { path: path.join(root, 'other.nprolog'), text: 'unrelated.\n' }])
  assert.deepEqual(inputs.dependencies, new Set([file, lib, leaf]))
  assert.deepEqual(inputs.buffers, [{ path: leaf, text: 'changed.\n' }])
  assert.equal(checkerInputs(file, source, [{ path: leaf, text: 'changed.\n' }]).signature, inputs.signature)
  assert.notEqual(checkerInputs(file, source, []).signature, inputs.signature)
})

test('input signatures use contents and track missing dependencies and configuration', t => {
  const { file, leaf, source, root } = fixture(t)
  const original = checkerInputs(file, source, []).signature
  fs.utimesSync(leaf, new Date(), new Date(Date.now() + 10000))
  assert.equal(checkerInputs(file, source, []).signature, original)
  fs.writeFileSync(leaf, 'different.\n')
  assert.notEqual(checkerInputs(file, source, []).signature, original)
  fs.unlinkSync(leaf)
  const missing = checkerInputs(file, source, [])
  assert.ok(missing.dependencies.has(leaf))
  fs.writeFileSync(leaf, 'leaf.\n')
  assert.equal(checkerInputs(file, source, []).signature, original)
  fs.writeFileSync(path.join(root, 'neoprolog.conf'), 'lib#test leaf.nprolog\n')
  assert.notEqual(checkerInputs(file, source, []).signature, original)
})

test('cyclic imports terminate and keep the root configuration for nested imports', t => {
  const { file, root, source } = fixture(t)
  const nested = path.join(root, 'nested'); fs.mkdirSync(nested)
  const lib = path.join(nested, 'lib.nprolog')
  fs.writeFileSync(path.join(root, 'neoprolog.conf'), 'lib#test nested/lib.nprolog\nleaf#test main.nprolog\n')
  fs.writeFileSync(path.join(nested, 'neoprolog.conf'), 'leaf#test wrong.nprolog\n')
  fs.writeFileSync(lib, '<- import "leaf#test".\nlib.\n')
  const inputs = checkerInputs(file, source, [])
  assert.deepEqual(inputs.dependencies, new Set([file, lib]))
  assert.equal(inputs.cwd, root)
})

test('open buffers override imported paths through symlinks', t => {
  const { file, root, leaf, source } = fixture(t)
  const alias = path.join(root, 'alias.nprolog'); fs.symlinkSync(leaf, alias)
  const inputs = checkerInputs(file, source, [{ path: alias, text: 'unsaved.\n' }])
  assert.deepEqual(inputs.buffers, [{ path: leaf, text: 'unsaved.\n' }])
})

test('editing import declarations refreshes the cached dependency closure', t => {
  const { file, lib, leaf, source } = fixture(t)
  const original = checkerInputs(file, source, [])
  const removed = checkerInputs(file, source, [{ path: lib, text: 'lib.\n' }])
  assert.ok(!removed.dependencies.has(leaf))
  assert.notEqual(removed.signature, original.signature)
  const restored = checkerInputs(file, source, [])
  assert.deepEqual(restored.dependencies, original.dependencies)
  assert.equal(restored.signature, original.signature)
})

test('compiler identity changes for replaced or missing executables', t => {
  const { root } = fixture(t), executable = path.join(root, 'compiler')
  const missing = executableIdentity(executable)
  fs.writeFileSync(executable, '#!/bin/sh\nexit 0\n', { mode: 0o755 })
  const existing = executableIdentity(executable)
  assert.notDeepEqual(existing, missing)
  fs.utimesSync(executable, new Date(), new Date(Date.now() + 10000))
  assert.notDeepEqual(executableIdentity(executable), existing)
})
