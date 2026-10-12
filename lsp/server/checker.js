'use strict'

const path = require('path')
const fs = require('fs')
const { pathToFileURL } = require('url')

// The compiler emits LSP-compatible, zero-based ranges. Imported-file
// diagnostics retain their location and link back from the checked document.
function compilerDiagnostics(stdout, filePath) {
  const rows = JSON.parse(stdout)
  if (!Array.isArray(rows)) throw new Error('expected a diagnostic array')
  return rows.map(d => {
    if (!d || typeof d.file !== 'string' || !d.file || typeof d.code !== 'string'
      || !validRange(d.range) || !['error', 'warning'].includes(d.severity) || typeof d.message !== 'string') {
      throw new Error('invalid compiler diagnostic')
    }
    const diagnostic = {
      range: d.range, message: d.message, code: d.code,
      severity: d.severity === 'error' ? 1 : 2, source: 'infera'
    }
    if (canonicalFile(d.file) !== canonicalFile(filePath)) {
      diagnostic.range = { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } }
      diagnostic.relatedInformation = [{
        location: { uri: pathToFileURL(path.resolve(d.file)).href, range: d.range },
        message: d.message
      }]
    }
    return diagnostic
  })
}

function validRange(range) {
  const position = p => p && Number.isInteger(p.line) && p.line >= 0
    && Number.isInteger(p.character) && p.character >= 0
  return range && position(range.start) && position(range.end)
    && (range.end.line > range.start.line
      || (range.end.line === range.start.line && range.end.character >= range.start.character))
}

// The compiler canonicalises source paths. Match symlinked workspaces and
// unsaved files as the same source rather than presenting them as imports.
function canonicalFile(file) {
  try { return fs.realpathSync(file) } catch {
    const parent = path.dirname(path.resolve(file))
    if (parent === path.resolve(file)) return parent
    return path.join(canonicalFile(parent), path.basename(file))
  }
}

module.exports = { compilerDiagnostics }
