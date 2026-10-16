'use strict'

const test = require('node:test')
const assert = require('node:assert/strict')
const fs = require('fs')
const os = require('os')
const path = require('path')
const { CONF_NAMES, findModuleContext, parseConf } = require('../server/modules')

function fixture(t) {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), 'infera-modules-')))
  t.after(() => fs.rmSync(root, { recursive: true, force: true }))
  const home = path.join(root, 'home')
  fs.mkdirSync(path.join(home, 'nprolog'), { recursive: true })
  return { root, home }
}

test('configuration names agree with the compiler', () => {
  const source = fs.readFileSync(path.join(__dirname, '../../src/Infera/Module.hs'), 'utf8')
  const names = [...source.match(/confNames = \[([^\]]+)\]/)[1].matchAll(/"([^"]+)"/g)].map(m => m[1])
  assert.deepEqual(CONF_NAMES, names)
})

test('the nearest supported configuration wins, with compiler filename priority', t => {
  const { root, home } = fixture(t)
  const project = path.join(root, 'project'), nested = path.join(project, 'nested'), source = path.join(nested, 'src')
  fs.mkdirSync(source, { recursive: true })
  fs.writeFileSync(path.join(project, 'neoprolog.conf'), '')
  fs.writeFileSync(path.join(nested, 'nprolog.conf'), '')
  assert.deepEqual(findModuleContext(source, home), { confPath: path.join(project, 'neoprolog.conf'), cwd: project })
  fs.writeFileSync(path.join(nested, 'infera.conf'), '')
  assert.deepEqual(findModuleContext(source, home), { confPath: path.join(nested, 'infera.conf'), cwd: nested })
  fs.writeFileSync(path.join(nested, 'neoprolog.conf'), '')
  assert.deepEqual(findModuleContext(source, home), { confPath: path.join(nested, 'neoprolog.conf'), cwd: nested })
})

test('home configuration fallback preserves the document cwd and its relative entries', t => {
  const { root, home } = fixture(t)
  const source = path.join(root, 'source')
  fs.mkdirSync(source)
  const confPath = path.join(home, 'nprolog', 'infera.conf')
  assert.deepEqual(findModuleContext(source, home), { confPath: null, cwd: source })
  fs.mkdirSync(path.join(source, 'neoprolog.conf')) // A directory is not a config file.
  fs.writeFileSync(confPath, 'lib#test lib.nprolog\n')
  const context = findModuleContext(source, home)
  assert.deepEqual(context, { confPath, cwd: source })
  assert.equal(parseConf(context.confPath, context.cwd).get('lib#test'), path.join(source, 'lib.nprolog'))
})

test('module mappings use the compiler whitespace format, last key and exact registration', t => {
  const { root } = fixture(t)
  const confPath = path.join(root, 'infera.conf')
  fs.writeFileSync(confPath, [
    '# comment', '', '  lib#old\t./old.nprolog  ', 'lib#old ./latest.nprolog',
    'other#test\t../other.nprolog', 'bad ./has a space.nprolog', 'missing', '#ignored x'
  ].join('\n'))
  const mappings = parseConf(confPath)
  assert.deepEqual([...mappings], [
    ['lib#old', path.join(root, 'latest.nprolog')], ['other#test', path.resolve(root, '../other.nprolog')]
  ])
  assert.equal(mappings.has('lib#new'), false, 'a stale hash cannot resolve by module name alone')
  assert.equal(parseConf(path.join(root, 'absent.conf')).size, 0)
})
