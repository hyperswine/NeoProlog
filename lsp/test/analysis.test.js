'use strict'

const test = require('node:test')
const assert = require('node:assert/strict')
const fs = require('fs')
const path = require('path')
const { tokenize, analyzeDocument, countArgs, predicateModifierPositions, IMPURE_BUILTIN_KEYS, TM } = require('../server/analysis')

test('tokenizer: CLP operators are not comments', () => {
  const toks = tokenize('p X <- X #= 1, X #!= 2, X #< 3, X #> 0, X #<= 5, X #>= 4. # comment')
  const ops = toks.filter(t => t.type === 'op').map(t => t.text)
  assert.deepEqual(ops, ['#=', '#!=', '#<', '#>', '#<=', '#>='])
  assert.equal(toks.filter(t => t.type === 'comment').length, 1)
})

test('tokenizer: a bare hash at EOF is still a comment', () => {
  for (const text of ['#', 'p. #', '#\n', '#\r\n']) {
    assert.deepEqual(tokenize(text).filter(t => t.type === 'comment').map(t => t.text.trim()), ['#'])
  }
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
})

test('declarations are extracted for hovers and highlighting', () => {
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
  assert.equal(a.decls.get('lonely')[0].arity, 1)
  assert.equal(a.decls.get('wrong')[0].arity, 3)
  assert.equal(a.predicateDefs.get('wrong')[0].arity, 2)
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
})

test('goals inside control constructs are references', () => {
  const a = analyzeDocument([
    'q 1.',
    'r 1.',
    'p X <- (q X -> r X ; not (q 2)), once (r X), findall Y (q Y) _, call q X.'
  ].join('\n'))
  assert.equal(a.predicateRefs.get('q').length, 4)
  assert.equal(a.predicateRefs.get('r').length, 2)
})

test('symbol extraction tolerates incomplete and invalid buffers without validating', () => {
  const a = analyzeDocument([
    'q 1.',
    'p X <- nope X, q X Y.',
    'lonely Z <- true.',
    '<- frobnicate.',
    'broken (X <- true.',
    'last X'
  ].join('\n'))
  assert.ok(a.predicateDefs.has('q'))
  assert.ok(a.predicateRefs.has('nope'))
  assert.ok(!Object.hasOwn(a, 'diagnostics'), 'only the compiler generates diagnostics')
  for (const text of ['p : det semidet.', 'p : (nonsense).', 'p : (', '<- import "bad".']) {
    assert.doesNotThrow(() => analyzeDocument(text))
  }
})

test('builtins, CLP goals and queries retain editor symbols', () => {
  const a = analyzeDocument([
    'puzzle X Y <- [X, Y] in 0..20, X + Y #= 10, X - Y #= 2, label [X, Y].',
    'sign N S <- (N > 0 -> S = pos ; N < 0 -> S = neg ; S = zero).',
    'w X <- write X, nl, str_concat "a" "b" _.',
    '> puzzle X Y?'
  ].join('\n'))
  assert.ok(a.predicateRefs.has('label'))
  assert.equal(a.queryPositions.size, 1)
})

test('the shipped examples retain predicate symbols', () => {
  const dir = path.join(__dirname, '..', '..', 'examples')
  for (const f of fs.readdirSync(dir).filter(n => n.endsWith('.nprolog'))) {
    const a = analyzeDocument(fs.readFileSync(path.join(dir, f), 'utf8'))
    assert.ok(a.predicateDefs.size > 0, f)
    assert.ok(!Object.hasOwn(a, 'diagnostics'))
  }
})

test('predicate flags style resolved arities, not data atoms or another overload', () => {
  const text = [
    'p : unsafe (int: <=).',
    'p : dynamic (int: <=) (int: =>).',
    'p 1.', 'p 1 2.',
    'both : unsafe dynamic.', 'both X.',
    'main <- p 1, p 1 2, p, both 1, wrapper p, call p 1, call (p 1) 2.',
    '# p 1, both 1', 'data "p both" p.',
    'nt : unsafe (any: <=>) (any: <=>).', 'nt -> [p].',
    'parse <- phrase nt "", emit nt.'
  ].join('\n')
  const a = analyzeDocument(text), mods = predicateModifierPositions(a)
  const line = n => a.tokens.filter(t => t.line === n && t.type === 'atom')
  const flags = t => mods.get(`${t.line}:${t.col}`) || 0
  assert.equal(flags(line(2)[0]), TM.unsafe)
  assert.equal(flags(line(3)[0]), TM.dynamic)
  assert.equal(flags(line(5)[0]), TM.unsafe | TM.dynamic)
  assert.deepEqual(line(6).filter(t => t.text === 'p').map(flags),
    [TM.unsafe, TM.dynamic, 0, 0, TM.unsafe, TM.dynamic])
  assert.equal(flags(line(6).find(t => t.text === 'both')), TM.unsafe | TM.dynamic)
  assert.equal(flags(line(8).at(-1)), 0)
  assert.equal(flags(line(10)[0]), TM.unsafe)
  assert.deepEqual(line(11).filter(t => t.text === 'nt').map(flags), [TM.unsafe, TM.unsafe])
  assert.equal(flags(line(11).find(t => t.text === 'emit')), TM.unsafe)
})

test('qualified and goal-taking calls preserve arity without treating templates as goals', () => {
  const a = analyzeDocument('main <- m:p 1, call m:p 1, phrase (m:p 1) "", findall (p X) (m:p X) R.')
  assert.deepEqual(a.qualifiedRefs.get('m').map(r => r.arity), [1, 1, 3, 1])
  assert.equal(a.predicateRefs.has('p'), false, 'findall template is data')
  const imported = analyzeDocument('p : unsafe (int: <=).\np : dynamic (int: <=) (any: <=>) (any: <=>).')
  const mods = predicateModifierPositions(a, alias => alias === 'm' ? imported : null)
  assert.deepEqual(a.qualifiedRefs.get('m').map(r => mods.get(`${r.predLoc.line}:${r.predLoc.col}`)),
    [TM.unsafe, TM.unsafe, TM.dynamic, TM.unsafe])
  assert.equal(predicateModifierPositions(a).size, 0)
})

test('effect styling agrees with compiler metadata and is arity aware, including DCG nl', () => {
  const purity = fs.readFileSync(path.join(__dirname, '../../src/Infera/Purity.hs'), 'utf8')
  const keys = [...purity.match(/impureBuiltinKeys =([\s\S]*?)\n  \]/)[1].matchAll(/\("([^"]+)", (\d+)\)/g)]
    .map(m => `${m[1]}/${m[2]}`)
  assert.deepEqual([...IMPURE_BUILTIN_KEYS].sort(), keys.sort())
  const a = analyzeDocument('main <- write X, nl, !, write X Y.\nline -> nl, { nl }.')
  const mods = predicateModifierPositions(a)
  assert.deepEqual(a.predicateRefs.get('write').map(r => mods.get(`${r.line}:${r.col}`) || 0), [TM.unsafe, 0])
  assert.deepEqual(a.predicateRefs.get('nl').map(r => mods.get(`${r.line}:${r.col}`) || 0), [TM.unsafe, 0, TM.unsafe])
  const cut = a.tokens.find(t => t.type === 'bang')
  assert.equal(mods.get(`${cut.line}:${cut.col}`), TM.unsafe)
})

test('goal-taking builtin overloads and DCG arities do not misclassify data atoms', () => {
  const a = analyzeDocument([
    'p : unsafe (any: <=>) (any: <=>).',
    'main <- phrase p, emit p X, once (p X) Y, minimize X p Y.',
    'grammar -> once p, phrase p, call p, { call p X Y }.'
  ].join('\n'))
  assert.deepEqual(a.predicateRefs.get('p').map(r => r.arity), [2, 2])
  const mods = predicateModifierPositions(a)
  for (const r of a.predicateRefs.get('p')) assert.equal(mods.get(`${r.line}:${r.col}`), TM.unsafe)
  const data = a.tokens.filter(t => t.text === 'p' && t.line === 1)
  assert.ok(data.every(t => !mods.has(`${t.line}:${t.col}`)))
})

test('flag styling is removed with edits and remains tolerant without producing diagnostics', () => {
  const first = analyzeDocument('p : unsafe dynamic.\np X.\nmain <- p 1.')
  assert.equal(predicateModifierPositions(first).size, 3)
  for (const text of ['p X.\nmain <- p 1.', 'p : (', 'main <- call (', '# p unsafe dynamic']) {
    const a = analyzeDocument(text)
    assert.equal(predicateModifierPositions(a).size, 0)
    assert.equal(Object.hasOwn(a, 'diagnostics'), false)
  }
})

test('extension contributes overridable underline styles and visible compiler suggestions by default', () => {
  const manifest = JSON.parse(fs.readFileSync(path.join(__dirname, '../package.json'), 'utf8'))
  const lock = JSON.parse(fs.readFileSync(path.join(__dirname, '../package-lock.json'), 'utf8'))
  assert.match(manifest.version, /^\d+\.\d+\.\d+$/)
  assert.equal(lock.version, manifest.version)
  assert.equal(lock.packages[''].version, manifest.version)
  assert.equal(manifest.contributes.configuration.properties['infera.performanceHints'].default, true)
  assert.deepEqual(manifest.contributes.semanticTokenModifiers.map(m => m.id), ['unsafe', 'dynamic'])
  assert.equal(manifest.contributes.configurationDefaults['[infera]']['editor.semanticHighlighting.enabled'], true)
  const rules = manifest.contributes.configurationDefaults['editor.semanticTokenColorCustomizations'].rules
  assert.deepEqual(rules['*.unsafe:infera'], { underline: true })
  assert.deepEqual(rules['*.dynamic:infera'], { underline: true })
})
