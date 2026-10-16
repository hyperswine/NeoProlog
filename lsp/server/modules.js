'use strict'

const fs = require('fs')
const path = require('path')
const os = require('os')

// Keep these names and the two-field format in agreement with Infera.Module.
// Local configurations set the checker cwd. The compiler's home fallback
// retains the source directory as cwd, including for relative module entries.
const CONF_NAMES = ['neoprolog.conf', 'infera.conf']

function pickConfInDir(dir) {
  for (const name of CONF_NAMES) {
    const candidate = path.join(dir, name)
    try { if (fs.statSync(candidate).isFile()) return candidate } catch {}
  }
  return null
}

function findModuleContext(startDir, homeDir = os.homedir()) {
  const sourceDir = path.resolve(startDir)
  let dir = sourceDir
  for (;;) {
    const conf = pickConfInDir(dir)
    if (conf) return { confPath: conf, cwd: dir }
    const parent = path.dirname(dir)
    if (parent === dir) break
    dir = parent
  }
  return { confPath: pickConfInDir(path.join(homeDir, 'nprolog')), cwd: sourceDir }
}

function parseConf(confPath, cwd = path.dirname(confPath)) {
  const map = new Map()
  let raw
  try { raw = fs.readFileSync(confPath, 'utf8') } catch { return map }
  for (const line of raw.split(/\r?\n/)) {
    if (line.startsWith('#')) continue
    const fields = line.trim().split(/\s+/)
    if (fields.length !== 2) continue
    map.set(fields[0], path.resolve(cwd, fields[1]))
  }
  return map
}

module.exports = { CONF_NAMES, findModuleContext, parseConf }
