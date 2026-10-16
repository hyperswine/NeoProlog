// analysis.js — tolerant tokenization and symbol extraction for editor features.
// Validation belongs exclusively to the compiler, including unsaved buffers.
//
// Pure functions (no LSP dependencies) so they can be unit-tested with node.
'use strict'

// ─── Documentation tables ──────────────────────────────────────────────────────

const BUILTIN_DOCS = {
  true: 'Always succeeds.',
  fail: 'Always fails.',
  false: 'Always fails.',
  nl: 'Writes a newline.',
  write: '`write Term` — writes Term (strings without quotes).',
  writeln: '`writeln Term` — writes Term followed by a newline.',
  print: '`print Term` — same as `write`.',
  call: '`call Goal Args...` — calls Goal with extra arguments appended. Cuts inside are local.',
  not: '`not Goal` — negation as failure.',
  once: '`once Goal` — commits to the first solution of Goal.',
  forall: '`forall Cond Action` — succeeds if Action holds for every solution of Cond.',
  findall: '`findall Template Goal List` — collects Template for every solution of Goal.',
  minimize: '`minimize Cost Goal` — returns the first least-cost answer of a finite search. Cost must be a ground integer in every answer; errors or incomplete search yield no optimum.',
  phrase: '`phrase NT List` — runs DCG non-terminal NT on List with an empty remainder.',
  is: '`Var is Expr` — evaluates the arithmetic expression Expr.',
  in: '`X in Lo..Hi` — CLP(Z) domain restriction; `inf`/`sup` for open bounds. A list on the left restricts every element.',
  label: '`label Vars` — CLP(Z) labeling: enumerates finite domains, smallest first.',
  labeling: '`labeling Vars` — same as `label`. `labeling [min Cost] Vars` returns one minimum using branch-and-bound over finite domains.',
  all_different: '`all_different Xs` — integer variables take distinct values; finite domains use global propagation.',
  reify: '`reify (A #<= B) Truth` — Truth is 0 or 1 and is equivalent to the integer relation; supports all six CLP comparisons.',
  all_distinct: '`all_distinct Xs` — same as `all_different`.',
  var: '`var X` — X is an unbound variable.',
  nonvar: '`nonvar X` — X is bound.',
  ground: '`ground X` — X contains no unbound variables.',
  is_int: '`is_int X` — X is an integer.',
  is_float: '`is_float X` — X is a float.',
  is_num: '`is_num X` — X is a number.',
  is_str: '`is_str X` — X is a string.',
  is_atom: '`is_atom X` — X is an atom.',
  is_char: '`is_char X` — X is a character.',
  is_list: '`is_list X` — X is a proper list.',
  str_concat: '`str_concat A B C` — C is A ++ B; with C bound, enumerates splits.',
  str_length: '`str_length S N` — N is the length of S.',
  str_chars: '`str_chars S Cs` — converts between a string and a list of characters.',
  str_atom: '`str_atom S A` — converts between a string and an atom.',
  str_num: '`str_num S N` — converts between a string and a number.',
  str_upper: '`str_upper S U` — upper-cases S.',
  str_lower: '`str_lower S L` — lower-cases S.',
  import: '`<- import "mod#hash".` — imports a registered module; its predicates are called as `mod:name`.',
  table: '`<- table.` — tabling on by default (the default).',
  unsafe: 'Flag: the predicate may perform effects (write, emit, read_file, cut, assert/retract) and call other unsafe predicates.',
  dynamic: 'Flag: the predicate has no clauses; its facts are added and removed with assert/retract.',
  notable: '`<- notable.` — tabling off by default.',
  index: '`<- index.` — argument indexing on (the default).',
  noindex: '`<- noindex.` — argument indexing off.',
  '=': '`A = B` — unification.',
  '==': '`A == B` — structural equality.',
  '!=': '`A != B` — delayed disequality constraint.',
  '#=': '`A #= B` — CLP(Z) equality.',
  '#!=': '`A #!= B` — CLP(Z) disequality.',
  '#<': '`A #< B` — CLP(Z) less-than.',
  '#>': '`A #> B` — CLP(Z) greater-than.',
  '#<=': '`A #<= B` — CLP(Z) less-or-equal.',
  '#>=': '`A #>= B` — CLP(Z) greater-or-equal.',
  '!': '`!` — cut: commits to the current clause and the choices made so far. Needs an `unsafe` declaration.',
  emit: '`emit NT` — prints the text described by DCG NT (first solution). Effect: needs `unsafe` outside queries.',
  read_file: '`read_file "path" S` — S is the contents of the file (a string literal path, read at load time). Effect.',
  phrase_from_file: '`phrase_from_file NT "path"` — parses the file with DCG NT. Effect.',
  assert: '`assert Fact` — adds a fact of a `dynamic` predicate (per branch). Effect.',
  retract: '`retract Fact` — removes a matching dynamic fact. Effect.',
  retractall: '`retractall Pattern` — removes every matching dynamic fact. Effect.',
  seq: '`seq Xs` (DCG) — the elements of a list or string in sequence.',
  wr: '`wr Term` (DCG) — the text of a term.',
  sp: '`sp` (DCG) — a space.',
  fmt: '`fmt "~w ~d ~s ~a ~n" Args` (DCG) — formatted text.',
  padl: '`padl Term Width` (DCG) — the text of Term right-aligned in Width.',
  padr: '`padr Term Width` (DCG) — the text of Term left-aligned in Width.',
  term_str: '`term_str Term S` — S is the text of Term.',
  str_lines: '`str_lines S Lines` — splits a string into lines.',
  char_code: '`char_code C N` — converts between a character and its code.',
  '->': '`(C -> T ; E)` — if-then-else; in a rule head, `->` defines a DCG rule.',
  ';': '`A ; B` — disjunction.'
}

const DECL_DOCS = {
  det: 'Exactly one solution. Failure is a determinism error; the first solution is committed to.',
  semidet: 'At most one solution. The first solution is committed to.',
  multi: 'At least one solution. Failure is a determinism error.',
  nondet: 'Any number of solutions (the default).',
  table: 'Force tabling (memoised fixpoint evaluation) for this predicate.',
  notable: 'Never table this predicate. Required for predicates with infinitely many answers.',
  index: 'Force argument indexing for this predicate.',
  noindex: 'Disable argument indexing for this predicate.',
  int: 'Integer sort.',
  float: 'Floating-point sort.',
  num: 'Integer or float.',
  str: 'String sort (`"..."`).',
  char: 'Character sort (`\'c\'`).',
  atom: 'Atom sort.',
  any: 'Any term (no check).',
  list: '`list <sort>` — proper list whose elements have the given sort.',
  '<=': 'Input mode: the argument must be ground when the predicate is called.',
  '=>': 'Output mode: the argument is ground after the call.',
  '<=>': 'In/out mode: no requirement.'
}

const DET_WORDS = ['det', 'semidet', 'multi', 'nondet']
const FLAG_WORDS = ['table', 'notable', 'index', 'noindex', 'unsafe', 'dynamic']
const SORT_WORDS = ['int', 'float', 'num', 'str', 'char', 'atom', 'any', 'list']
const DIRECTIVES = new Set(['import', 'table', 'notable', 'index', 'noindex'])

const KEYWORD_ATOMS = new Set(['true', 'fail', 'false', 'nl', 'not', 'once', 'call', 'forall', 'findall', 'minimize', 'write', 'writeln', 'print', 'phrase', 'is', 'in', 'label', 'labeling', 'import'])

const BUILTIN_PREDICATES = new Set(Object.keys(BUILTIN_DOCS).filter(k => /^[a-z]/.test(k)))

// Styling metadata, mirrored from Infera.Purity.impureBuiltinKeys. The test
// suite checks agreement; the compiler still owns effect validation.
const IMPURE_BUILTIN_KEYS = new Set([
  'write/1', 'writeln/1', 'print/1', 'nl/0', 'emit/1', 'read_file/2',
  'phrase_from_file/2', 'assert/1', 'retract/1', 'retractall/1', '!/0'
])

// ─── Semantic token legend ─────────────────────────────────────────────────────

const TOKEN_TYPES = ['keyword', 'comment', 'string', 'number', 'operator', 'variable', 'function', 'parameter', 'namespace', 'type']
const TOKEN_MODIFIERS = ['declaration', 'unsafe', 'dynamic']
const TT = { keyword: 0, comment: 1, string: 2, number: 3, operator: 4, variable: 5, function: 6, parameter: 7, namespace: 8, type: 9 }
const TM = { declaration: 1, unsafe: 2, dynamic: 4 }

// ─── Tokenizer ─────────────────────────────────────────────────────────────────

const MULTI_OPS = ['<=>', '#>=', '#<=', '#!=', '<-', '->', '<=', '=>', '::', '..', '#=', '#<', '#>', '>=', '==', '!=']

function tokenize(text) {
  const tokens = []
  let i = 0, line = 0, col = 0
  let sawSpace = true

  function advance() {
    if (text[i] === '\n') { line++; col = 0 } else { col++ }
    i++
  }
  function push(type, start, sl, sc) {
    tokens.push({ type, text: text.slice(start, i), line: sl, col: sc, adjPrev: !sawSpace })
    sawSpace = false
  }

  while (i < text.length) {
    const c = text[i]
    if (c === ' ' || c === '\t' || c === '\r' || c === '\n') { sawSpace = true; advance(); continue }
    const sl = line, sc = col, si = i

    if (c === '#' && !/[=!<>]/.test(text[i + 1] || '')) {
      while (i < text.length && text[i] !== '\n') advance()
      push('comment', si, sl, sc)
      sawSpace = true
      continue
    }
    if (c === '"') {
      advance()
      while (i < text.length && text[i] !== '"') {
        if (text[i] === '\\') advance()
        if (i < text.length) advance()
      }
      if (i < text.length) advance()
      push('string', si, sl, sc)
      continue
    }
    if (c === "'") {
      advance()
      if (i < text.length && text[i] === '\\') advance()
      if (i < text.length) advance()
      if (i < text.length && text[i] === "'") advance()
      push('charlit', si, sl, sc)
      continue
    }
    if (/[0-9]/.test(c)) {
      while (i < text.length && /[0-9]/.test(text[i])) advance()
      if (text[i] === '.' && /[0-9]/.test(text[i + 1] || '')) {
        advance()
        while (i < text.length && /[0-9]/.test(text[i])) advance()
        push('float', si, sl, sc)
      } else {
        push('integer', si, sl, sc)
      }
      continue
    }
    if (/[A-Z_]/.test(c)) {
      while (i < text.length && /[a-zA-Z0-9_]/.test(text[i])) advance()
      push(text.slice(si, i) === '_' ? 'anon' : 'variable', si, sl, sc)
      continue
    }
    if (/[a-z]/.test(c)) {
      while (i < text.length && /[a-zA-Z0-9_]/.test(text[i])) advance()
      push('atom', si, sl, sc)
      continue
    }

    let matched = false
    for (const op of MULTI_OPS) {
      if (text.startsWith(op, i)) {
        for (let k = 0; k < op.length; k++) advance()
        const type = op === '<-' ? 'neck' : op === '->' ? 'dcgneck' : 'op'
        push(type, si, sl, sc)
        matched = true
        break
      }
    }
    if (matched) continue

    advance()
    switch (c) {
      case ':': push('colon', si, sl, sc); break
      case '.': push(/[a-zA-Z_]/.test(text[i] || '') ? 'opdot' : 'dot', si, sl, sc); break
      case ',': push('comma', si, sl, sc); break
      case ';': push('semi', si, sl, sc); break
      case '!': push('bang', si, sl, sc); break
      case '(': push('lparen', si, sl, sc); break
      case ')': push('rparen', si, sl, sc); break
      case '[': push('lbracket', si, sl, sc); break
      case ']': push('rbracket', si, sl, sc); break
      case '{': push('lbrace', si, sl, sc); break
      case '}': push('rbrace', si, sl, sc); break
      case '|': push('pipe', si, sl, sc); break
      case '?': push('qmark', si, sl, sc); break
      default:
        if ('+-*/%^><='.includes(c)) push('op', si, sl, sc)
        else push('unknown', si, sl, sc)
    }
  }
  return tokens
}

// ─── Helpers ───────────────────────────────────────────────────────────────────

const OPENERS = new Set(['lparen', 'lbracket', 'lbrace'])
const CLOSERS = new Set(['rparen', 'rbracket', 'rbrace'])

function addToMap(map, key, value) {
  if (!map.has(key)) map.set(key, [])
  map.get(key).push(value)
}

function loc(tok) { return { line: tok.line, col: tok.col, length: tok.text.length } }

/** Index of the token matching the opener at `start`, or -1. */
function matchingClose(tokens, start) {
  let depth = 0
  for (let i = start; i < tokens.length; i++) {
    if (OPENERS.has(tokens[i].type)) depth++
    else if (CLOSERS.has(tokens[i].type)) { depth--; if (depth === 0) return i }
  }
  return -1
}

/** Split tokens at depth-0 tokens of the given types. */
function splitTop(tokens, types) {
  const parts = []
  let cur = [], depth = 0
  for (const t of tokens) {
    if (OPENERS.has(t.type)) depth++
    else if (CLOSERS.has(t.type)) depth--
    if (depth === 0 && types.has(t.type)) { parts.push(cur); cur = []; continue }
    cur.push(t)
  }
  parts.push(cur)
  return parts
}

/**
 * Count the arguments of `name args...` at depth 0.  Returns null when a
 * depth-0 infix operator makes the shape ambiguous.
 */
function countArgs(tokens) {
  let n = 0
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i]
    if (OPENERS.has(t.type)) {
      const j = matchingClose(tokens, i)
      n++
      i = j < 0 ? tokens.length : j
      continue
    }
    if (['atom', 'variable', 'anon', 'integer', 'float', 'string', 'charlit'].includes(t.type)) { n++; continue }
    if (t.type === 'op' && (t.text === '-' || t.text === '+') && tokens[i + 1] && ['integer', 'float'].includes(tokens[i + 1].type) && tokens[i + 1].adjPrev) {
      // signed numeric literal
      n++; i++; continue
    }
    if (t.type === 'op' || t.type === 'opdot' || t.type === 'colon') return null
    return null
  }
  return n
}

/** Conservative term boundaries for the arguments of goal-taking builtins. */
function argumentGroups(tokens) {
  const groups = []
  for (let i = 0; i < tokens.length; i++) {
    const first = tokens[i]
    if (OPENERS.has(first.type)) {
      const end = matchingClose(tokens, i)
      if (end < 0) return null
      groups.push(tokens.slice(i, end + 1)); i = end
    } else if (['atom', 'variable', 'anon', 'integer', 'float', 'string', 'charlit'].includes(first.type)) {
      if (first.type === 'atom' && tokens[i + 1]?.type === 'colon' && tokens[i + 1].adjPrev
        && tokens[i + 2]?.type === 'atom' && tokens[i + 2].adjPrev) {
        groups.push(tokens.slice(i, i + 3)); i += 2
      } else groups.push([first])
    } else if (first.type === 'op' && ['-', '+'].includes(first.text)
      && ['integer', 'float'].includes(tokens[i + 1]?.type) && tokens[i + 1].adjPrev) {
      groups.push(tokens.slice(i, i + 2)); i++
    } else return null
  }
  return groups
}

// ─── Declarations ──────────────────────────────────────────────────────────────

function parseDeclaration(tokens, ctx) {
  // tokens: atom colon ... (terminator excluded)
  const name = tokens[0]
  const rest = tokens.slice(2)
  const words = { det: [], flags: [], args: [] }
  const mark = (tok, kind) => ctx.declWordKinds.set(`${tok.line}:${tok.col}`, kind)
  let i = 0
  while (i < rest.length) {
    const t = rest[i]
    if (t.type === 'atom' && DET_WORDS.includes(t.text)) { words.det.push(t); mark(t, 'determinism'); i++; continue }
    if (t.type === 'atom' && FLAG_WORDS.includes(t.text)) { words.flags.push(t); mark(t, 'flag'); i++; continue }
    if (t.type === 'op' && ['<=', '=>', '<=>'].includes(t.text)) { words.args.push({ sort: 'any', mode: t.text }); mark(t, 'mode'); i++; continue }
    if (t.type === 'lparen') {
      const j = matchingClose(rest, i)
      if (j < 0) {
        break
      }
      const inner = rest.slice(i + 1, j)
      const spec = { sort: 'any', mode: '<=>' }
      let k = 0
      const sortParts = []
      while (k < inner.length) {
        const u = inner[k]
        if (u.type === 'atom' && SORT_WORDS.includes(u.text)) { sortParts.push(u.text); mark(u, 'sort'); k++; continue }
        if (u.type === 'anon') { sortParts.push('any'); mark(u, 'sort'); k++; continue }
        if (u.type === 'lparen' || u.type === 'rparen') { k++; continue }
        if (u.type === 'colon') { k++; continue }
        if (u.type === 'op' && ['<=', '=>', '<=>'].includes(u.text)) { spec.mode = u.text; mark(u, 'mode'); k++; continue }
        k++
      }
      if (sortParts.length) spec.sort = sortParts.join(' ')
      words.args.push(spec)
      i = j + 1
      continue
    }
    i++
  }
  const flagsOnly = words.det.length === 0 && words.args.length === 0
  const text = tokens.map((t, k) => (k > 0 && !t.adjPrev ? ' ' : '') + t.text).join('') + '.'
  return {
    name: name.text,
    arity: flagsOnly ? null : words.args.length,
    det: words.det.length ? words.det[0].text : null,
    flags: words.flags.map(f => f.text),
    args: words.args,
    flagsOnly,
    text,
    ...loc(name)
  }
}

// ─── Goals ─────────────────────────────────────────────────────────────────────

function collectGoals(tokens, ctx, opts) {
  const dcg = !!(opts && opts.dcg)
  const segments = splitTop(tokens, new Set(['comma', 'semi', 'dcgneck']))
  for (const seg of segments) collectGoal(seg, ctx, dcg)
}

function collectGoal(seg, ctx, dcg) {
  if (seg.length === 0) return
  const first = seg[0]

  // ( ... ) as a whole goal → recurse (control constructs)
  if (first.type === 'lparen' && matchingClose(seg, 0) === seg.length - 1) {
    collectGoals(seg.slice(1, -1), ctx, { dcg })
    return
  }
  // { Goal } inside a DCG body
  if (first.type === 'lbrace' && matchingClose(seg, 0) === seg.length - 1) {
    collectGoals(seg.slice(1, -1), ctx, { dcg: false })
    return
  }
  if (first.type === 'bang') {
    ctx.effectPositions.add(`${first.line}:${first.col}`)
    return
  }
  if (first.type === 'lbracket' || first.type === 'string') return
  if (first.type !== 'atom') {
    // operator goal such as `X is Y`, `A #= B`, or a variable goal
    return
  }

  // Qualified call mod:pred
  const second = seg[1], third = seg[2]
  if (second && second.type === 'colon' && second.adjPrev && third && third.type === 'atom' && third.adjPrev) {
    const arity = countArgs(seg.slice(3))
    addToMap(ctx.qualifiedRefs, first.text, { pred: third.text, modLoc: loc(first), predLoc: loc(third),
      arity: arity === null ? null : arity + (dcg ? 2 : 0), dcg })
    ctx.namespacePositions.add(`${first.line}:${first.col}`)
    ctx.qualColonPositions.add(`${second.line}:${second.col}`)
    return
  }

  const args = seg.slice(1)
  const arity = countArgs(args)
  addToMap(ctx.predicateRefs, first.text, { ...loc(first), arity: arity === null ? null : arity + (dcg ? 2 : 0), dcg })

  const groups = argumentGroups(args)
  if (!groups) return
  const goalArgs = { not: [1, [0]], once: [1, [0]], forall: [2, [0, 1]], findall: [3, [1]], minimize: [2, [1]] }
  const control = goalArgs[first.text]
  for (const i of !dcg && control?.[0] === groups.length ? control[1] : []) {
    if (groups[i]) collectGoals(groups[i], ctx, { dcg: false })
  }
  if (first.text === 'call' && groups.length) {
    collectCallable(groups[0], ctx, groups.length - 1 + (dcg ? 2 : 0))
  } else if (!dcg && ((['phrase', 'phrase_from_file'].includes(first.text) && groups.length === 2)
    || (first.text === 'emit' && groups.length === 1))) {
    collectCallable(groups[0], ctx, 2)
  }
}

function collectCallable(tokens, ctx, extraArity) {
  if (tokens[0]?.type === 'lparen' && matchingClose(tokens, 0) === tokens.length - 1) {
    tokens = tokens.slice(1, -1)
  }
  const [first, second, third] = tokens
  if (first?.type !== 'atom') return
  const qualified = second?.type === 'colon' && second.adjPrev && third?.type === 'atom' && third.adjPrev
  const arity = countArgs(tokens.slice(qualified ? 3 : 1))
  if (arity === null) return
  if (qualified) {
    addToMap(ctx.qualifiedRefs, first.text, { pred: third.text, modLoc: loc(first), predLoc: loc(third), arity: arity + extraArity })
    ctx.namespacePositions.add(`${first.line}:${first.col}`)
    ctx.qualColonPositions.add(`${second.line}:${second.col}`)
  } else addToMap(ctx.predicateRefs, first.text, { ...loc(first), arity: arity + extraArity, dcg: false })
}

// This is symbol styling, not an independent validator. Ambiguous calls have
// no modifiers; flags from another arity or an unrelated imported name do not
// leak onto a token. Name-wide declarations apply to every resolved arity.
function predicateModifiers(a, name, arity, declaration = false) {
  if (arity === null && !declaration) return 0
  const flags = new Set((a.decls.get(name) || [])
    .filter(d => d.flagsOnly || d.arity === arity).flatMap(d => d.flags))
  return (flags.has('unsafe') ? TM.unsafe : 0) | (flags.has('dynamic') ? TM.dynamic : 0)
}

function predicateModifierPositions(a, resolveImport = () => null) {
  const positions = new Map()
  const set = (where, mods) => {
    if (mods) positions.set(`${where.line}:${where.col}`, (positions.get(`${where.line}:${where.col}`) || 0) | mods)
  }
  for (const [name, defs] of a.predicateDefs) {
    for (const def of defs) set(def, predicateModifiers(a, name, def.arity))
  }
  for (const [name, decls] of a.decls) {
    for (const decl of decls) set(decl, predicateModifiers(a, name, decl.arity, true))
  }
  for (const [name, refs] of a.predicateRefs) {
    for (const ref of refs) set(ref, predicateModifiers(a, name, ref.arity)
      | (IMPURE_BUILTIN_KEYS.has(`${name}/${ref.arity}`) ? TM.unsafe : 0))
  }
  for (const [alias, refs] of a.qualifiedRefs) {
    const imported = resolveImport(alias)
    if (!imported) continue
    for (const ref of refs) set(ref.predLoc, predicateModifiers(imported, ref.pred, ref.arity))
  }
  for (const key of a.effectPositions) positions.set(key, TM.unsafe)
  return positions
}

// ─── Document analysis ─────────────────────────────────────────────────────────

function analyzeDocument(text) {
  const tokens = tokenize(text)
  const ctx = {
    predicateDefs: new Map(),
    predicateRefs: new Map(),
    qualifiedRefs: new Map(),
    decls: new Map(),
    imports: [],
    queryPositions: new Set(),
    headPositions: new Set(),
    namespacePositions: new Set(),
    qualColonPositions: new Set(),
    importKeyPositions: new Set(),
    directivePositions: new Set(),
    declNamePositions: new Set(),
    declWordKinds: new Map(),
    effectPositions: new Set()
  }

  // Split into items at depth-0 terminators.
  const items = []
  let current = [], depth = 0
  for (const tok of tokens) {
    if (tok.type === 'comment') continue
    if (OPENERS.has(tok.type)) depth++
    else if (CLOSERS.has(tok.type)) depth = Math.max(0, depth - 1)
    current.push(tok)
    if ((tok.type === 'dot' || tok.type === 'qmark') && depth === 0) {
      items.push({ tokens: current })
      current = []
    }
  }
  if (current.length > 0) {
    items.push({ tokens: current })
  }

  for (const item of items) {
    const toks = item.tokens
    const last = toks[toks.length - 1]
    const hasTerm = last.type === 'dot' || last.type === 'qmark'
    const body = hasTerm ? toks.slice(0, -1) : toks
    if (body.length === 0) continue
    const first = body[0]

    // Inline query
    if (first.type === 'op' && first.text === '>') {
      ctx.queryPositions.add(`${first.line}:${first.col}`)
      collectGoals(body.slice(1), ctx, {})
      continue
    }

    // Directive
    if (first.type === 'neck') {
      const goals = body.slice(1)
      const head = goals[0]
      if (head && head.type === 'atom' && head.text === 'import' && goals[1] && goals[1].type === 'string') {
        const raw = goals[1].text.slice(1, -1)
        ctx.imports.push({ modId: raw, alias: raw.split('#')[0], ...loc(goals[1]) })
        ctx.importKeyPositions.add(`${head.line}:${head.col}`)
      } else if (head && head.type === 'atom' && DIRECTIVES.has(head.text) && goals.length === 1) {
        ctx.directivePositions.add(`${head.line}:${head.col}`)
      }
      continue
    }

    // Declaration: `name : ...` (colon not glued to the name as in mod:pred)
    if (first.type === 'atom' && body[1] && body[1].type === 'colon' && !(body[1].adjPrev && body[2] && body[2].adjPrev && body[2].type === 'atom')) {
      const decl = parseDeclaration(body, ctx)
      addToMap(ctx.decls, decl.name, decl)
      ctx.declNamePositions.add(`${first.line}:${first.col}`)
      ctx.declWordKinds.set(`${body[1].line}:${body[1].col}`, 'colon')
      continue
    }

    // Clause: head [<- body | -> dcgbody]
    let neckIdx = -1, d = 0
    for (let i = 0; i < body.length; i++) {
      const t = body[i]
      if (OPENERS.has(t.type)) d++
      else if (CLOSERS.has(t.type)) d--
      else if ((t.type === 'neck' || t.type === 'dcgneck') && d === 0) { neckIdx = i; break }
    }
    const isDcg = neckIdx >= 0 && body[neckIdx].type === 'dcgneck'
    const headToks = neckIdx >= 0 ? body.slice(0, neckIdx) : body
    const bodyToks = neckIdx >= 0 ? body.slice(neckIdx + 1) : []

    if (headToks.length === 0 || headToks[0].type !== 'atom') {
      continue
    }
    const headAtom = headToks[0]
    const baseArity = countArgs(headToks.slice(1))
    const arity = baseArity === null ? null : baseArity + (isDcg ? 2 : 0)
    addToMap(ctx.predicateDefs, headAtom.text, { ...loc(headAtom), arity, dcg: isDcg, hasBody: neckIdx >= 0 })
    ctx.headPositions.add(`${headAtom.line}:${headAtom.col}`)

    if (neckIdx >= 0) collectGoals(bodyToks, ctx, { dcg: isDcg })

  }

  return { tokens, ...ctx }
}

module.exports = {
  tokenize,
  analyzeDocument,
  countArgs,
  predicateModifierPositions,
  IMPURE_BUILTIN_KEYS,
  BUILTIN_DOCS,
  DECL_DOCS,
  BUILTIN_PREDICATES,
  KEYWORD_ATOMS,
  DET_WORDS,
  FLAG_WORDS,
  SORT_WORDS,
  TOKEN_TYPES,
  TOKEN_MODIFIERS,
  TT,
  TM
}
