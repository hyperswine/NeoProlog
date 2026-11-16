'use strict'

const path = require('path')
const fs = require('fs')
const { pathToFileURL } = require('url')

const SEVERITIES = { error: 1, warning: 2, information: 3, hint: 4 }

// `check --json` reports {diagnostics, predicates}; older compilers report
// the diagnostic array alone. Predicate facts (recursion verdicts) are kept
// for the checked document only.
function compilerReport(stdout, filePath) {
  const parsed = JSON.parse(stdout)
  const rows = Array.isArray(parsed) ? parsed : parsed && parsed.diagnostics
  const facts = !Array.isArray(parsed) && parsed && Array.isArray(parsed.predicates) ? parsed.predicates : []
  const predicates = facts.filter(p => p && typeof p.file === 'string' && typeof p.name === 'string'
    && Number.isInteger(p.arity) && Number.isInteger(p.line) && typeof p.recursion === 'string'
    && typeof p.verdict === 'string' && canonicalFile(p.file) === canonicalFile(filePath))
  return { diagnostics: diagnosticRows(rows, filePath), predicates }
}

function compilerDiagnostics(stdout, filePath) {
  return compilerReport(stdout, filePath).diagnostics
}

// The compiler emits LSP-compatible, zero-based ranges. Imported-file
// diagnostics retain their location and link back from the checked document.
function diagnosticRows(rows, filePath) {
  if (!Array.isArray(rows)) throw new Error('expected a diagnostic array')
  return rows.map(d => {
    if (!d || typeof d.file !== 'string' || !d.file || typeof d.code !== 'string'
      || !validRange(d.range) || !Object.hasOwn(SEVERITIES, d.severity) || typeof d.message !== 'string') {
      throw new Error('invalid compiler diagnostic')
    }
    const diagnostic = {
      range: d.range, message: d.message, code: d.code,
      severity: SEVERITIES[d.severity], source: 'infera'
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

function visibleDiagnostics(diagnostics, settings) {
  return settings.performanceHints === false
    ? diagnostics.filter(d => d.severity === 1 || !String(d.code).startsWith('perf-')) : diagnostics
}

module.exports = { compilerReport, compilerDiagnostics, visibleDiagnostics, canonicalFile }
