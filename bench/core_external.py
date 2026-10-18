#!/usr/bin/env python3
"""Checked loaded-query comparison against SWI-Prolog and Scryer.

This module builds argument vectors and parses captured engine output; importing
it never launches an engine. Algorithms and inputs in ``core-external.pl`` match
``core-major.hs``. Run the commands from the repository root, for example::

    swipl -q -g "external_bench_swipl('core-loop',100),halt" -t halt bench/core-external.pl > /tmp/core-swipl.txt
    python3 bench/core_external.py swipl core-loop 100 < /tmp/core-swipl.txt
    scryer-prolog -f --no-add-history -g "use_module(library(time)),external_bench_scryer('core-nrev',100),halt" bench/core-external.pl > /tmp/core-scryer.txt
    python3 bench/core_external.py scryer core-nrev 100 < /tmp/core-scryer.txt
    python3 -m unittest discover -s test -p '*bench_harness_test.py'

Use ``command`` when orchestrating multiple samples, check the process exit code
and pass its stderr to ``parse_sample``. Increase the batch until the returned
``comparison_timing_sufficient`` flag is true (at least 50 ms of batch CPU).
Scryer's library(time) timer is coarse and supplies no loaded wall-time value.
The driver drains and checks every query, warms up before timing, and prints
its complete checked result after timing. Process startup and loading are not
part of these measurements.
"""
import ast
import json
import math
import re
import sys
from pathlib import Path

CASES = ('core-nrev', 'core-loop', 'core-fib', 'core-queens')
DRIVER = str(Path(__file__).with_name('core-external.pl'))
MIN_GATE_BATCH_CPU_SECONDS = 0.05


def command(engine, binary, case, batch):
    if case not in CASES or type(batch) is not int or not 0 < batch <= 1000000:
        raise ValueError('unsupported case or batch')
    if engine == 'swipl':
        goal = "external_bench_swipl('%s',%d),halt" % (case, batch)
        return [str(binary), '-q', '-g', goal, '-t', 'halt', DRIVER]
    if engine == 'scryer':
        goal = "use_module(library(time)),external_bench_scryer('%s',%d),halt" % (case, batch)
        return [str(binary), '-f', '--no-add-history', '-g', goal, DRIVER]
    raise ValueError('unsupported engine')


def unique(prefix, stdout):
    values = [line.lstrip()[len(prefix):] for line in stdout.splitlines()
              if line.lstrip().startswith(prefix)]
    if len(values) != 1:
        raise ValueError('expected exactly one ' + prefix + ' line')
    return values[0]


def positive(value):
    seconds = float(value)
    if not math.isfinite(seconds) or seconds <= 0:
        raise ValueError('CPU/wall duration must be positive and finite; increase batch')
    return seconds


def parse_sample(engine, case, batch, stdout, stderr=''):
    if engine not in ('swipl', 'scryer'):
        raise ValueError('unsupported engine')
    if case not in CASES or type(batch) is not int or not 0 < batch <= 1000000:
        raise ValueError('unsupported case or batch')
    if re.search(r'\b(?:error|exception)\s*[:(]|search depth limit', stdout + stderr, re.I):
        raise ValueError('engine reported an error or exhausted search')
    if unique('INFERA_CORE_OK:', stdout) != case:
        raise ValueError('incorrect completion marker')
    try:
        answers = ast.literal_eval(unique('INFERA_CORE_RESULT:', stdout))
    except (SyntaxError, ValueError) as error:
        raise ValueError('malformed collected result') from error
    if type(answers) is not list or len(answers) != 1:
        raise ValueError('expected exactly one fully collected answer')
    value = answers[0]
    if case in ('core-loop', 'core-fib'):
        expected = 90000 if case == 'core-loop' else 75025
        valid = type(value) is int and value == expected
    elif case == 'core-nrev':
        valid = type(value) is list and all(type(x) is int for x in value) and value == list(range(30, 0, -1))
    else:
        valid = (type(value) is list and all(type(x) is int for x in value)
                 and sorted(value) == list(range(1, 9))
                 and all(abs(a - b) != j - i for i, a in enumerate(value)
                         for j, b in enumerate(value) if i < j))
    if not valid:
        raise ValueError('independent result model failed')
    if engine == 'swipl':
        cpu = positive(unique('INFERA_CORE_CPU_SECONDS:', stdout))
        wall = positive(unique('INFERA_CORE_WALL_SECONDS:', stdout))
    elif engine == 'scryer':
        values = re.findall(r'^\s*% CPU time: ([0-9]+(?:\.[0-9]+)?)s, [0-9]+(?:_[0-9]+)* inferences\s*$',
                            stdout, flags=re.M)
        if len(values) != 1:
            raise ValueError('expected exactly one Scryer library(time) CPU line')
        cpu = positive(values[0])
        wall = None
    else:
        raise ValueError('unsupported engine')
    return {'engine': engine, 'case': case, 'batch_queries': batch,
            'result': answers, 'fully_drained': True, 'independent_checked': True,
            'warmup_queries': 1, 'startup_included': False, 'output_included': False,
            'cpu_seconds': cpu, 'wall_seconds': wall,
            'per_query_cpu_seconds': cpu / batch,
            'per_query_wall_seconds': wall / batch if wall is not None else None,
            'comparison_timing_sufficient': cpu >= MIN_GATE_BATCH_CPU_SECONDS,
            'minimum_gate_batch_cpu_seconds': MIN_GATE_BATCH_CPU_SECONDS}


if __name__ == '__main__':
    if len(sys.argv) != 4:
        raise SystemExit('usage: core_external.py swipl|scryer CASE BATCH < stdout.txt')
    print(json.dumps(parse_sample(sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.stdin.read())))
