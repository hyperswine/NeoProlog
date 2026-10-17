'use strict'

const fs = require('fs')
const path = require('path')
const { createHash } = require('crypto')
const { analyzeDocument } = require('./analysis')
const { canonicalFile } = require('./checker')
const { findModuleContext, parseConf } = require('./modules')

// Only source text determines imports. Repeated saves still fingerprint disk
// inputs, but need not tokenize their unchanged contents again. Bound this
// cache independently of how many projects have been opened in the session.
const importCache = new Map()
function importsOf(file, text) {
  const cached = importCache.get(file)
  if (cached?.text === text) return cached.imports
  const imports = analyzeDocument(text).imports
  importCache.delete(file)
  importCache.set(file, { text, imports })
  if (importCache.size > 256) importCache.delete(importCache.keys().next().value)
  return imports
}

// The compiler uses the root's module configuration for the entire import
// expansion. Open buffers override disk by canonical identity, including
// missing files and symlinked workspaces.
function checkerInputs(filePath, source, buffers) {
  const root = canonicalFile(filePath)
  const context = findModuleContext(path.dirname(filePath))
  const conf = context.confPath ? parseConf(context.confPath, context.cwd) : new Map()
  const open = new Map(buffers.map(buffer => [canonicalFile(buffer.path), buffer]))
  const sources = new Map(), snapshots = [], readErrors = new Map()
  const read = file => {
    try { return fs.readFileSync(file, 'utf8') } catch (error) { readErrors.set(file, error.code); return null }
  }
  function visit(file, text) {
    const key = canonicalFile(file)
    if (sources.has(key)) return
    const buffer = open.get(key)
    if (text === undefined) text = buffer ? buffer.text : read(key)
    sources.set(key, text)
    if (key !== root && buffer) snapshots.push({ path: key, text })
    if (text === null) return
    for (const imported of importsOf(key, text)) {
      // Symbol extraction deliberately does not parse language string
      // escapes. Keep the dependency set conservative for escaped imports.
      if (imported.modId.includes('\\')) {
        for (const candidate of conf.values()) visit(candidate)
      }
      const dependency = conf.get(imported.modId)
      if (dependency) visit(dependency)
    }
  }
  visit(root, source)
  const signature = createHash('sha256').update(JSON.stringify([
    root, context.cwd, context.confPath, context.confPath ? read(context.confPath) : null,
    [...sources].sort(([a], [b]) => a.localeCompare(b)),
    [...readErrors].sort(([a], [b]) => a.localeCompare(b))
  ])).digest('hex')
  return { ...context, source, buffers: snapshots, dependencies: new Set(sources.keys()), signature }
}

function executableIdentity(executable) {
  const candidates = path.isAbsolute(executable) || executable.includes(path.sep)
    ? [path.resolve(executable)]
    : (process.env.PATH || '').split(path.delimiter).map(dir => path.join(dir, executable))
  for (const candidate of candidates) {
    try {
      fs.accessSync(candidate, fs.constants.X_OK)
      const stat = fs.statSync(candidate)
      if (stat.isFile()) return [executable, canonicalFile(candidate), stat.size, stat.mtimeMs, stat.ctimeMs]
    } catch {}
  }
  return [executable, null]
}

module.exports = { checkerInputs, executableIdentity }
