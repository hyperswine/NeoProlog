'use strict'

const test = require('node:test')
const assert = require('node:assert/strict')
const fs = require('fs')
const path = require('path')
const { tokenize, analyzeDocument, countArgs } = require('../server/analysis')

const messages = a => a.diagnostics.map(d => d.message)

test('tokenizer: CLP operators are not comments', () => {
  const toks = tokenize('p X <- X #= 1, X #!= 2, X #< 3, X #>= 4. # comment')
  const ops = toks.filter(t => t.type === 'op').map(t => t.text)
  assert.deepEqual(ops, ['#=', '#!=', '#<', '#>='])
  assert.equal(toks.filter(t => t.type === 'comment').length, 1)
})

test('tokenizer: modes, ranges and control tokens', () => {
  const toks = tokenize('f : det (int: <=) (int: =>) <=>.\ng X <- (X in 1..3 -> ! ; fail).')
  const texts = toks.map(t => t.text)
  for (const s of ['<=', '=>', '<=>', '..', '->', '!', ';']) assert.ok(texts.includes(s), s)
})

test('countArgs counts top-level argument groups', () => {
  const args = tokenize('X (foo Y) [1, 2 | T] "s" -5 bar').filter(t => t.type !== 'comment')
  assert.equal(countArgs(args), 6)
  assert.equal(countArgs(tokenize('X + 1')), null)
})

test('predicates are keyed by name with arity, DCG adds two', () => {
  const a = analyzeDocument([
    'append [] L L.',
    'append [H | T] L [H | R] <- append T L R.',
    'greeting -> [hello], name.',
    'name -> [world].'
  ].join('\n'))
  assert.deepEqual(a.predicateDefs.get('append').map(d => d.arity), [3, 3])
  assert.deepEqual(a.predicateDefs.get('greeting').map(d => d.arity), [2])
  assert.deepEqual(a.predicateRefs.get('name').map(r => r.arity), [2])
  assert.deepEqual(messages(a), [])
})

test('declarations are parsed and matched against clauses', () => {
  const a = analyzeDocument([
    'fact : det (int: <=) (int: =>).',
    'fact 0 1.',
    'fact N R <- N > 0, N1 is N - 1, fact N1 R1, R is N * R1.',
    'gen : notable.',
    'gen 0.',
    'gen N <- gen M, N is M + 1.',
    'lonely : semidet (str: <=).',
    'wrong : det (any: <=) (any: =>) (any: =>).',
    'wrong X Y <- Y = X.'
  ].join('\n'))
  const fact = a.decls.get('fact')[0]
  assert.equal(fact.arity, 2)
  assert.equal(fact.det, 'det')
  assert.deepEqual(fact.args.map(x => `${x.sort}:${x.mode}`), ['int:<=', 'int:=>'])
  assert.equal(fact.text, 'fact : det (int: <=) (int: =>).')
  assert.equal(a.decls.get('gen')[0].flagsOnly, true)
  assert.ok(messages(a).some(m => m.includes('`lonely/1` is declared but has no clauses')))
  assert.ok(messages(a).some(m => m.includes('declaration is for `wrong/3`')))
  assert.equal(a.declWordKinds.get('0:7'), 'determinism')
  assert.equal(a.declWordKinds.get('0:12'), 'sort')
  assert.equal(a.declWordKinds.get('0:17'), 'mode')
})

test('mod:pred is a qualified call, not a declaration', () => {
  const a = analyzeDocument('<- import "facts#abc".\nmain R <- facts:factorial 4 R.')
  assert.equal(a.imports.length, 1)
  assert.equal(a.imports[0].alias, 'facts')
  assert.equal(a.qualifiedRefs.get('facts')[0].pred, 'factorial')
  assert.equal(a.decls.size, 0)
  assert.deepEqual(messages(a), [])
})

test('goals inside control constructs are references', () => {
  const a = analyzeDocument([
    'q 1.',
    'r 1.',
    'p X <- (q X -> r X ; not (q 2)), once (r X), findall Y (q Y) _, call q X.'
  ].join('\n'))
  assert.equal(a.predicateRefs.get('q').length, 4)
  assert.equal(a.predicateRefs.get('r').length, 2)
  assert.deepEqual(messages(a), [])
})

test('diagnostics: undefined predicates, wrong arity, singletons, syntax', () => {
  const a = analyzeDocument([
    'q 1.',
    'p X <- nope X, q X Y.',
    'lonely Z <- true.',
    '<- frobnicate.',
    'broken (X <- true.',
    'last X'
  ].join('\n'))
  const ms = messages(a)
  assert.ok(ms.some(m => m.includes('`nope` is not defined')))
  assert.ok(ms.some(m => m.includes('no clauses for `q/2`')))
  assert.ok(ms.some(m => m.includes('singleton variable Y')))
  assert.ok(ms.some(m => m.includes('singleton variable Z')))
  assert.ok(ms.some(m => m.includes('unbalanced brackets')))
  assert.ok(ms.some(m => m.includes('unknown directive')))
  assert.ok(ms.some(m => m.includes("missing '.'")))
  assert.ok(!ms.some(m => m.includes('singleton variable X')), 'X in p is used twice')
})

test('builtins, CLP goals and operator goals raise no diagnostics', () => {
  const a = analyzeDocument([
    'puzzle X Y <- [X, Y] in 0..20, X + Y #= 10, X - Y #= 2, label [X, Y].',
    'sign N S <- (N > 0 -> S = pos ; N < 0 -> S = neg ; S = zero).',
    'w X <- write X, nl, str_concat "a" "b" _.',
    '> puzzle X Y?'
  ].join('\n'))
  assert.deepEqual(messages(a), [])
  assert.equal(a.queryPositions.size, 1)
})

test('the shipped examples analyse without errors', () => {
  const dir = path.join(__dirname, '..', '..', 'examples')
  for (const f of fs.readdirSync(dir).filter(n => n.endsWith('.nprolog'))) {
    const a = analyzeDocument(fs.readFileSync(path.join(dir, f), 'utf8'))
    const errors = a.diagnostics.filter(d => d.severity === 1)
    assert.deepEqual(errors, [], `${f}: ${errors.map(e => e.message).join('; ')}`)
  }
})
