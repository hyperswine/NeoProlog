'use strict'

const test = require('node:test')
const assert = require('node:assert/strict')
const fs = require('fs')
const path = require('path')
const { Registry, INITIAL } = require('vscode-textmate')
const onig = require('vscode-oniguruma')
const { tokenize } = require('../server/analysis')

// Exercise the same TextMate/Oniguruma engine as VS Code, including state
// carried over from preceding lines; JavaScript regex tests are insufficient.
let grammarPromise
function grammar() {
  if (!grammarPromise) grammarPromise = (async () => {
    await onig.loadWASM(fs.readFileSync(require.resolve('vscode-oniguruma/release/onig.wasm')))
    const raw = JSON.parse(fs.readFileSync(path.join(__dirname, '../syntaxes/infera.tmLanguage.json'), 'utf8'))
    const registry = new Registry({
      onigLib: Promise.resolve(onig),
      loadGrammar: async scope => scope === raw.scopeName ? raw : null
    })
    return registry.loadGrammar(raw.scopeName)
  })()
  return grammarPromise
}

async function highlight(source) {
  const g = await grammar()
  let state = INITIAL
  return source.split(/\r?\n/).map(line => {
    const result = g.tokenizeLine(line, state)
    state = result.ruleStack
    return result.tokens.map(t => ({ start: t.startIndex, end: t.endIndex,
      text: line.slice(t.startIndex, t.endIndex), scopes: t.scopes }))
  })
}

function checkToken(lines, line, start, text, scope) {
  for (let col = start; col < start + text.length; col++) {
    const token = lines[line].find(t => t.start <= col && col < t.end)
    assert.ok(token?.scopes.includes(scope), `${text}: ${JSON.stringify(token)}`)
    if (scope === 'keyword.operator.infera') {
      assert.ok(!token.scopes.some(s => s.startsWith('comment.')), `${text} is a comment`)
    }
  }
}

test('TextMate: every CLP operator stays an operator next to comments', async () => {
  for (const op of ['#=', '#!=', '#<', '#>', '#<=', '#>=']) {
    for (const source of [`X ${op} 2 # trailing`, `X${op}2 # trailing`,
      `  ${op} 2 # trailing`, `# heading\nX ${op} 2 # trailing`]) {
      const lines = await highlight(source)
      const parts = source.split('\n'), line = parts.length - 1
      checkToken(lines, line, parts[line].indexOf(op), op, 'keyword.operator.infera')
      checkToken(lines, line, parts[line].indexOf('# trailing'), '# trailing', 'comment.line.number-sign.infera')
    }
  }
})

test('TextMate and semantic lexer agree across the entire Minesweeper source', async () => {
  const source = fs.readFileSync(path.join(__dirname, '../../examples/minesweeper.nprolog'), 'utf8')
  const lines = await highlight(source)
  let operators = 0
  for (const token of tokenize(source)) {
    if (token.type === 'op' && token.text.startsWith('#')) {
      checkToken(lines, token.line, token.col, token.text, 'keyword.operator.infera')
      operators++
    } else if (token.type === 'comment') {
      checkToken(lines, token.line, token.col, token.text, 'comment.line.number-sign.infera')
    }
  }
  assert.ok(operators >= 4, 'test the actual #= and #<= goals, including tile_cols')
})

test('TextMate: hashes in quoted strings and characters do not start comments', async () => {
  const source = String.raw`p "say \"hi\" # not a comment" '#' <- X #= 1. # real comment`
  const lines = await highlight(source)
  checkToken(lines, 0, source.indexOf('# not'), '# not', 'string.quoted.double.infera')
  checkToken(lines, 0, source.indexOf("'#'") + 1, '#', 'string.quoted.single.infera')
  checkToken(lines, 0, source.indexOf('#='), '#=', 'keyword.operator.infera')
  checkToken(lines, 0, source.indexOf('# real'), '# real comment', 'comment.line.number-sign.infera')
})

test('TextMate: comment lines containing CLP examples end at the newline', async () => {
  const source = '# X #= 2 and Y #<= 3\nCount #= Sum,\nCount #<= Max.\n#'
  const lines = await highlight(source)
  checkToken(lines, 0, 0, source.split('\n')[0], 'comment.line.number-sign.infera')
  checkToken(lines, 1, 6, '#=', 'keyword.operator.infera')
  checkToken(lines, 2, 6, '#<=', 'keyword.operator.infera')
  checkToken(lines, 3, 0, '#', 'comment.line.number-sign.infera')
})
