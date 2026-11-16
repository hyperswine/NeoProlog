#!/usr/bin/env python3
"""Independent checks of one JSON relation in parsing/generation/checking modes."""
import argparse
import ast
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def quote(text):
    # Infera source literals use Haskell escapes, not JSON's \u notation.
    escapes = {'"': '\\"', '\\': '\\\\', '\n': '\\n', '\r': '\\r', '\t': '\\t', '\b': '\\b', '\f': '\\f'}
    return '"' + ''.join(escapes.get(c, '\\' + str(ord(c)) + '\\&' if ord(c) < 32 else c) for c in text) + '"'


def term(value):
    if value is None: return 'null'
    if value is True: return 'true'
    if value is False: return 'false'
    if isinstance(value, (int, float)): return f'(num {value!r})'
    if isinstance(value, str): return f'(str {quote(value)})'
    if isinstance(value, list): return '(array [' + ','.join(map(term, value)) + '])'
    return '(object [' + ','.join(f'(pair {quote(k)} {term(v)})' for k,v in value.items()) + '])'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('binary', type=Path)
    args = ap.parse_args()
    binary = args.binary.resolve()
    source = (ROOT / 'examples/json_relation.nprolog').read_text().split('\n> ', 1)[0]
    values = [None, True, False, 0, -17, 123456789012345678901234567890,
              1.25, -0.125, '', 'quote " slash / backslash \\', 'line\n\t\b\f\r',
              ''.join(map(chr,range(32))), 'λ🙂', [], {}, [1,True,None,'x'],
              {'name':'Ada','scores':[3,5],'active':True}, {'nested':{'xs':[[],{}]}}]
    checks = []
    for value in values:
        text = json.dumps(value,ensure_ascii=False,separators=(',',':'))
        checks += [f'json {quote(text)} Parsed, Parsed = {term(value)}',
                   f'json {quote(" \r\n\t"+text+" \t")} _']
    for text in ['1e2', '-2.5E+2', '1e-3', '"\\u03bb\\ud83d\\ude42"', '"\\/"']:
        value = json.loads(text)
        checks.append(f'json {quote(text)} Parsed, Parsed = {term(value)}')
    invalid = ['', ' ', 'null trailing', '[1,]', '{"x":1,}', '{x:1}', '[01]',
               '+1', '.5', '1.', '1e', '1e+', '--1', 'NaN', 'Infinity',
               'TRUE', '"unterminated', '"\\q"', '"raw\nnewline"', '\vnull',
               '{"x" 1}', '[true false]', '{"x":}']
    def bad_constant(value):
        raise ValueError(value)
    for text in invalid:
        try:
            json.loads(text,parse_constant=bad_constant)
        except ValueError:
            pass
        else:
            raise AssertionError(('invalid fixture accepted by Python', text))
        checks.append(f'not (json {quote(text)} _)')
    checks += [
        'json "{\\"kind\\":\\"temperature\\",\\"value\\":21}" (object [pair "kind" (str "temperature"),pair "value" (num Reading)]), Reading = 21',
        'json "[1,2,3]" (array [num 1,num 2,num 3])',
        'not (json "[1,2,3]" (array [num 1,num 2,num 4]))',
        'json "{\\"x\\":1,\\"x\\":2}" (object [pair "x" (num 1),pair "x" (num 2)])',
        'not (json _ (num not_a_number))',
        'not (json _ (str not_a_string))',
        'not (json _ (array [num 1 | bad_tail]))',
        'findall T (member B [true,false], json T (object [pair "active" B])) Ts, Ts = ["{\\"active\\":true}","{\\"active\\":false}"]',
    ]
    program = source + '\n' + '\n'.join(f'case_{i} <- {goal}.\n> case_{i}?' for i,goal in enumerate(checks))
    for i,value in enumerate(values):
        program += f'\ngenerate_{i} Codes <- json Text {term(value)}, str_chars Text Cs, maplist char_code Cs Codes.\n> generate_{i} Codes?\n'
    for jit,stream in [('0','0'),('0','1'),('1','0'),('1','1')]:
        env={**os.environ,'INFERA_JIT':jit,'INFERA_CORE_STREAM':stream}
        with tempfile.TemporaryDirectory(prefix='infera-json-relation-') as d:
            file=Path(d)/'demo.nprolog'; file.write_text(program)
            result=subprocess.run([str(binary),str(file)],input=':quit\n',text=True,
                                  capture_output=True,cwd=d,env=env,timeout=30)
            assert result.returncode==0, result
            assert not re.search(r'Error:|^false\.|depth limit',result.stdout,re.M),result.stdout+result.stderr
            assert len(re.findall(r'^true\.$',result.stdout,re.M))==len(checks),result.stdout
            encoded=re.findall(r'^Codes = (.+)$',result.stdout,re.M)
            assert len(encoded)==len(values),result.stdout
            for raw,expected in zip(encoded,values):
                text=''.join(map(chr,ast.literal_eval(raw)))
                actual=json.loads(text,parse_constant=bad_constant)
                assert actual==expected,(text,actual,expected)
            print(json.dumps({'status':'ok','jit':jit,'stream':stream,
                              'relation_checks':len(checks),'generated_documents':len(values)}),flush=True)


if __name__=='__main__': main()
