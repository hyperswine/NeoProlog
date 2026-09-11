#!/usr/bin/env node
// build.js — build a Dash docset from docs/website.
//
// Usage: node docs/dash/build.js
// Output: docs/dash/dist/Infera.docset and docs/dash/dist/Infera.tgz
//
// Index entries come from elements with data-dash="Type:Name" in the HTML
// (plus one Guide entry per page).  Requires the `sqlite3` CLI and `tar`.
'use strict'

const fs = require('fs')
const path = require('path')
const { execFileSync } = require('child_process')

const ROOT = path.resolve(__dirname, '..', '..')
const SITE = path.join(ROOT, 'docs', 'website')
const DIST = path.join(__dirname, 'dist')
const DOCSET = path.join(DIST, 'Infera.docset')
const CONTENTS = path.join(DOCSET, 'Contents')
const RESOURCES = path.join(CONTENTS, 'Resources')
const DOCUMENTS = path.join(RESOURCES, 'Documents')

const INFO_PLIST = `<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>CFBundleIdentifier</key><string>infera</string>
  <key>CFBundleName</key><string>Infera</string>
  <key>DocSetPlatformFamily</key><string>infera</string>
  <key>isDashDocset</key><true/>
  <key>isJavaScriptEnabled</key><true/>
  <key>dashIndexFilePath</key><string>index.html</string>
  <key>DashDocSetFamily</key><string>dashtoc</string>
  <key>DashDocSetFallbackURL</key><string>https://hyperswine.github.io/NeoProlog/</string>
</dict>
</plist>
`

function unescapeHtml(s) {
  return s.replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&#39;/g, "'").replace(/&amp;/g, '&')
}

function sqlQuote(s) { return "'" + String(s).replace(/'/g, "''") + "'" }

function main() {
  fs.rmSync(DIST, { recursive: true, force: true })
  fs.mkdirSync(DOCUMENTS, { recursive: true })
  fs.writeFileSync(path.join(CONTENTS, 'Info.plist'), INFO_PLIST)

  const rows = []
  const pages = fs.readdirSync(SITE).filter(f => f.endsWith('.html')).sort()

  for (const file of pages) {
    let html = fs.readFileSync(path.join(SITE, file), 'utf8')
    const title = (html.match(/<title>(.*?)<\/title>/) || [, file])[1].replace(/ · Infera$/, '')
    rows.push(['Guide', title === 'Infera' ? 'Overview' : title, file])

    // Every element with data-dash="Type:Name" gets an index row and a
    // Dash table-of-contents anchor placed just before it.
    html = html.replace(/<(\w+)([^>]*?)\sid="([^"]+)"([^>]*?)\sdata-dash="([^"]+)"([^>]*)>/g, (m, tag, a, id, b, dash, c) => {
      const [type, ...rest] = unescapeHtml(dash).split(':')
      const name = rest.join(':')
      rows.push([type, name, `${file}#${id}`])
      const anchor = `<a name="//apple_ref/cpp/${encodeURIComponent(type)}/${encodeURIComponent(name)}" class="dashAnchor"></a>`
      return `${anchor}<${tag}${a} id="${id}"${b}${c}>`
    })
    fs.writeFileSync(path.join(DOCUMENTS, file), html)
  }
  for (const file of fs.readdirSync(SITE).filter(f => !f.endsWith('.html'))) {
    fs.copyFileSync(path.join(SITE, file), path.join(DOCUMENTS, file))
  }

  const sql = [
    'CREATE TABLE searchIndex(id INTEGER PRIMARY KEY, name TEXT, type TEXT, path TEXT);',
    'CREATE UNIQUE INDEX anchor ON searchIndex (name, type, path);',
    ...rows.map(([type, name, p]) => `INSERT OR IGNORE INTO searchIndex(name, type, path) VALUES (${sqlQuote(name)}, ${sqlQuote(type)}, ${sqlQuote(p)});`)
  ].join('\n')
  execFileSync('sqlite3', [path.join(RESOURCES, 'docSet.dsidx')], { input: sql })

  execFileSync('tar', ['--exclude=.DS_Store', '-czf', path.join(DIST, 'Infera.tgz'), '-C', DIST, 'Infera.docset'])
  console.log(`built ${DOCSET} (${rows.length} index entries) and Infera.tgz`)
}

main()
