'use strict'
const { test } = require('node:test')
const assert = require('node:assert/strict')
const { recursionActions } = require('../server/recursionActions')
const uri = 'file:///test.nprolog'
const diagnostic = (code, message) => ({ code, message, range: { start: { line: 0, character: 0 }, end: { line: 0, character: 4 } } })
test('partial recursion offers marker and a non-executable guard reminder', () => {
  const result = recursionActions(uri, 'p X <- p X.', [diagnostic('partial-recursion', 'integer descent needs a preceding lower/upper guard; add `p : unsafe.`')])
  assert.equal(result.length, 2)
  assert.match(result[0].edit.changes[uri][0].newText, /p : unsafe\./)
  assert.match(result[1].edit.changes[uri][0].newText, /^# TODO:/)
})
test('removing unsafe preserves other flags and comments', () => {
  const d = diagnostic('unnecessary-unsafe', '')
  const edit = text => recursionActions(uri, text, [d])[0].edit.changes[uri][0].newText
  assert.equal(edit('p : unsafe notable. # keep'), 'p : notable. # keep')
  assert.equal(edit('p : unsafe.'), '')
  assert.equal(edit('p : det (int: <=) unsafe.'), 'p : det (int: <=).')
  assert.equal(edit('ns:p : unsafe notable.'), 'ns:p : notable.')
})

test('marker insertion is outside a multiline clause and ignores imported diagnostics', () => {
  const d = diagnostic('partial-recursion', 'add `p : unsafe.`')
  d.range.start.line = 3
  const actions = recursionActions(uri, 'p X <-\n  X > 0,\n  Y is X - 1,\n  p Y.', [d])
  assert.equal(actions[0].edit.changes[uri][0].range.start.line, 0)
  assert.deepEqual(recursionActions(uri, '', [{ ...d, relatedInformation: [{}] }]), [])
})
