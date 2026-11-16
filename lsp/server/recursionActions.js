'use strict'

// Compiler messages name the declaration to edit; never invent an executable
// guard, since a termination repair can change the relation's answers.
function recursionActions(uri, text, diagnostics) {
  const lines = text.split(/\r?\n/)
  const actions = []
  const action = (title, diagnostic, range, newText) => ({
    title, kind: 'quickfix', diagnostics: [diagnostic],
    edit: { changes: { [uri]: [{ range, newText }] } }
  })
  const start = line => ({ start: { line, character: 0 }, end: { line, character: 0 } })
  for (const d of diagnostics) {
    if (d.relatedInformation?.length) continue // imported source needs its own document edit

    if (d.code === 'partial-recursion') {
      const name = /add `([^`]+) : unsafe\.`/.exec(d.message)?.[1]
      if (!name) continue
      actions.push(action(`Mark ${name} unsafe`, d, start(0),
        `# Recursion is not proven total; callers must acknowledge partiality.\n${name} : unsafe.\n`))
      if (/lower\/upper guard/.test(d.message)) {
        actions.push(action('Add a reminder to bound the integer recursion', d, start(0),
          '# TODO: add a lower or upper guard that bounds the recursive integer measure.\n'))
      }
    } else if (d.code === 'unnecessary-unsafe') {
      const line = d.range.start.line
      const source = lines[line] || ''
      // Edit only a complete, single-line declaration. Ignore tokens in
      // signature parentheses and preserve the rest of the signature.
      const match = /^(\s*\S+\s*:\s*)([^.]+)(\.\s*(?:#.*)?)$/.exec(source)
      if (!match) continue
      let depth = 0
      let quote = null
      const removable = []
      for (let i = 0; i < match[2].length; i++) {
        const ch = match[2][i]
        if (quote) {
          if (ch === '\\') i++
          else if (ch === quote) quote = null
        } else if (ch === "'" || ch === '"') quote = ch
        else if (ch === '(' || ch === '[') depth++
        else if (ch === ')' || ch === ']') depth--
        else if (depth === 0 && /^unsafe\b/.test(match[2].slice(i)) && (i === 0 || /\s/.test(match[2][i - 1]))) removable.push(i)
      }
      if (!removable.length) continue
      let body = match[2]
      for (const offset of removable.reverse()) body = body.slice(0, offset) + body.slice(offset + 6)
      body = body.trim()
      const replacement = body ? match[1] + body + match[3] : (match[3].includes('#') ? match[3].slice(match[3].indexOf('#')) : '')
      actions.push(action('Remove unnecessary unsafe marker', d,
        { start: { line, character: 0 }, end: { line, character: source.length } }, replacement))
    }
  }
  return actions
}
module.exports = { recursionActions }
