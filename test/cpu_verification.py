#!/usr/bin/env python3
"""Independent finite CPU model, proof reports and mutation tests.

python3 test/cpu_verification.py /path/to/infera --all-modes
No solver or third-party Python packages are required.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
CLAIMS = ('add_contract sub_contract add_commutative add_sub_inverse add_zero sub_self '
          'inc_contract dec_contract inc_dec_inverse dec_inc_inverse immediate_normalization '
          'ldb_preserves movb_preserves nop_frame halt_frame branch_contract '
          'transition_functional countdown_rank countdown_all_inputs halt_absorbs').split()
REPRESENTATIVES = (0, 1, 127, 128, 255)
ROW = re.compile(r'\[(-?\d+(?:,\s*-?\d+)*)\]')


def execute(op, state):
    """A separate imperative specification; never calls Infera's alu_spec."""
    pc, a, b, z, c = state
    if isinstance(op, tuple):
        name, arg = op
        if name == 'lda': a, z, c = arg & 255, int((arg & 255) == 0), 0
        elif name == 'ldb': b = arg & 255
        elif name == 'jmp': return arg, a, b, z, c
        elif name == 'jz' and z: return arg, a, b, z, c
        elif name == 'jnz' and not z: return arg, a, b, z, c
    elif op == 'add':
        total = a + b
        a, c = total & 255, int(total > 255)
        z = int(a == 0)
    elif op == 'sub': a, c = (a - b) & 255, 0; z = int(a == 0)
    elif op == 'inc': c = int(a == 255); a = (a + 1) & 255; z = int(a == 0)
    elif op == 'dec': a, c = (a - 1) & 255, 0; z = int(a == 0)
    elif op == 'mova': a, z, c = b, int(b == 0), 0
    elif op == 'movb': b = a
    elif op == 'hlt': return state
    elif op != 'nop': raise AssertionError(op)
    return pc + 1, a, b, z, c


class Runner:
    def __init__(self, binary, directory, source, env):
        self.binary, self.directory, self.source, self.env = binary, directory, source, env
        self.queries = self.transitions = 0

    def query(self, goal, source=None):
        self.queries += 1
        path = self.directory / f'cpu{self.queries}.nprolog'
        path.write_text((self.source if source is None else source) + '\n> ' + goal + '?\n')
        result = subprocess.run([str(self.binary), str(path), '+RTS', '-N1', '-RTS'],
                                input=':quit\n', capture_output=True, text=True,
                                env=self.env, cwd=self.directory, timeout=180)
        assert result.returncode == 0 and 'Error:' not in result.stdout + result.stderr, (
            goal, result.returncode, result.stdout[-1200:], result.stderr)
        return result.stdout

    def rows(self, goal, source=None):
        text = self.query('findall Row (' + goal + ') Rows', source=source)
        answers = re.findall(r'^Rows = (.+)$', text, re.M)
        assert len(answers) == 1, text[-1000:]
        serialized = answers[0]
        assert serialized.startswith('[') and serialized.endswith(']'), serialized[:200]
        body = serialized[1:-1]
        position = 0
        for match in ROW.finditer(body):
            assert body[position:match.start()].strip() == (',' if position else ''), body[position:match.start()]
            position = match.end()
            yield tuple(map(int, match[1].split(',')))
        assert not body[position:].strip(), body[position:position+200]

    def matrix(self, op, flags):
        z, c = flags
        goal = (f'byte_value A, byte_value B, execute {op} (cpu 11 A B {z} {c}) '
                '(cpu P R OB Z C), Row = [A,B,P,R,OB,Z,C]')
        count = 0
        for row in self.rows(goal):
            a, b = divmod(count, 256)
            assert row == (a, b, *execute(op, (11, a, b, z, c))), (op, flags, row)
            count += 1
        assert count == 256 * 256, (op, flags, count)
        self.transitions += count

    def other_instructions(self):
        for op in ('inc', 'dec', 'mova', 'movb', 'nop', 'hlt'):
            domains = 'representative A, byte_value B' if op == 'mova' else 'byte_value A, representative B'
            expected = ((a, b, z, c) for a in (REPRESENTATIVES if op == 'mova' else range(256))
                        for b in (range(256) if op == 'mova' else REPRESENTATIVES)
                        for z in (0, 1) for c in (0, 1))
            goal = (f'{domains}, flag_value Z0, flag_value C0, execute {op} '
                    '(cpu 11 A B Z0 C0) (cpu P R OB Z C), Row = [A,B,Z0,C0,P,R,OB,Z,C]')
            actual = list(self.rows(goal))
            wanted = [(a, b, z, c, *execute(op, (11, a, b, z, c))) for a, b, z, c in expected]
            assert actual == wanted, op
            self.transitions += len(actual)
        for op in ('lda', 'ldb'):
            goal = (f'Lo is 0 - 256, between Lo 511 I, flag_value Z0, flag_value C0, '
                    f'execute ({op} I) (cpu 11 73 141 Z0 C0) (cpu P A B Z C), '
                    'Row = [I,Z0,C0,P,A,B,Z,C]')
            actual = list(self.rows(goal))
            wanted = [(i, z, c, *execute((op, i), (11, 73, 141, z, c)))
                      for i in range(-256, 512) for z in (0, 1) for c in (0, 1)]
            assert actual == wanted, op
            self.transitions += len(actual)
        for op in ('jmp', 'jz', 'jnz'):
            goal = (f'between 0 7 T, between 0 7 P0, representative A, representative B, '
                    f'flag_value Z0, flag_value C0, execute ({op} T) (cpu P0 A B Z0 C0) '
                    '(cpu P R OB Z C), Row = [T,P0,A,B,Z0,C0,P,R,OB,Z,C]')
            actual = list(self.rows(goal))
            wanted = [(t, p, a, b, z, c, *execute((op, t), (p, a, b, z, c)))
                      for t in range(8) for p in range(8) for a in REPRESENTATIVES
                      for b in REPRESENTATIVES for z in (0, 1) for c in (0, 1)]
            assert actual == wanted, op
            self.transitions += len(actual)

    def proofs_and_mutants(self):
        report = self.query('proof_suite Report')
        expected = 'Report = [' + ', '.join('result ' + name + ' proved' for name in CLAIMS) + ']'
        assert expected in report, report[-2500:]
        assert 'Rows = []' in self.query('findall R (check nonexistent R) Rows')
        assert 'Witness = input 255 got 256' in self.query('once (mutant_counterexample no_wrap Witness)')
        assert 'Witness = inputs 1 255' in self.query('once (mutant_counterexample lost_carry Witness)')
        assert 'Witness = input 0' in self.query('once (mutant_counterexample undefined_flag Witness)')
        add = re.search(r'^execute add .*?\.\n', self.source, re.M | re.S)[0]
        changes = [
            ('add_contract', self.source.replace('R is S % 256', 'R is S', 1)),
            ('add_contract', self.source.replace(add, '', 1)),
            ('add_contract', self.source + '\n' + add),
            ('add_contract', self.source.replace('cflag S C <- C is S / 256.', 'cflag _ 0.')),
            ('ldb_preserves', self.source.replace('(cpu Q A R Z C) <- R is I % 256', '(cpu Q A R _ C) <- R is I % 256')),
        ]
        for name, mutation in changes:
            assert mutation != self.source
            result = self.query('check ' + name + ' Result', source=mutation)
            assert 'Result = refuted ' in result, (name, result[-2000:])
        rows = list(self.rows('alu_spec add 255 B 0 1 1, label [B], Row = [B]'))
        assert rows == [(1,)], rows

    def programs(self):
        for name, initial, steps, expected in [
            ('addition', (0, 0, 0, 0, 0), 3, (3, 245, 200, 0, 0)),
            ('overflow', (0, 0, 0, 0, 0), 3, (3, 44, 100, 0, 1))]:
            state = 'cpu ' + ' '.join(map(str, initial))
            actual = list(self.rows(f'run {name} ({state}) {steps} (cpu P A B Z C), Row = [P,A,B,Z,C]'))
            assert actual == [expected], (name, actual)
        actual = list(self.rows('byte_value N, Steps is 2 + 3*N, run (countdown N) (cpu 0 0 0 0 0) Steps '
                                '(cpu P A B Z C), Row = [N,Steps,P,A,B,Z,C]'))
        wanted = []
        for n in range(256):
            rom = {0: ('lda', n), 1: ('jz', 4), 2: 'dec', 3: ('jmp', 1), 4: 'hlt'}
            state, steps = (0, 0, 0, 0, 0), 0
            while state[0] != 4:
                state = execute(rom[state[0]], state)
                steps += 1
                assert steps <= 767
            assert steps == 2 + 3 * n
            wanted.append((n, steps, *state))
        assert actual == wanted
        companion = (ROOT / 'examples/my8bitcpu.nprolog').read_text().split('\n> ', 1)[0]
        for op, pc, next_pc, expected_b in [('ldb', 1, 2, 100), ('movb', 9, 10, 23)]:
            code = companion + ('\ninstr 9 movb.' if op == 'movb' else '')
            actual = list(self.rows(f'between 0 1 Z0, between 0 1 C0, step (cpu {pc} 23 91 Z0 C0) '
                                    '(cpu P A B Z C), Row = [Z0,C0,P,A,B,Z,C]', source=code))
            assert actual == [(z, c, next_pc, 23, expected_b, z, c) for z in (0, 1) for c in (0, 1)]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('binary', type=Path)
    ap.add_argument('--all-modes', action='store_true')
    args = ap.parse_args()
    source = (ROOT / 'examples/8bitcpu.nprolog').read_text().split('\n> ', 1)[0]
    modes = [('1', '1'), ('0', '1'), ('1', '0'), ('0', '0')] if args.all_modes else [('1', '1')]
    for jit, stream in modes:
        start = time.monotonic()
        with tempfile.TemporaryDirectory(prefix='infera-cpu-') as directory:
            runner = Runner(args.binary.resolve(), Path(directory), source,
                            {**os.environ, 'INFERA_JIT': jit, 'INFERA_CORE_STREAM': stream})
            runner.proofs_and_mutants()
            for op in ('add', 'sub'):
                for z in (0, 1):
                    for c in (0, 1):
                        runner.matrix(op, (z, c))
            runner.other_instructions()
            runner.programs()
            print(json.dumps({'status': 'ok', 'jit': jit, 'stream': stream,
                              'claims': len(CLAIMS), 'mutations_rejected': 5,
                              'independent_transitions': runner.transitions,
                              'queries': runner.queries, 'seconds': round(time.monotonic() - start, 3)}), flush=True)


if __name__ == '__main__':
    main()
