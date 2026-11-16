#!/usr/bin/env python3
"""Keep shipped std modules and examples explicit about unproven recursion."""
import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    binary = str(args.binary.resolve())
    files = sorted(ROOT.glob('std/*.nprolog')) + sorted(ROOT.glob('examples/*.nprolog'))
    count = 0
    for path in files:
        result = subprocess.run([binary, 'check', '--json', str(path), '+RTS', '-N1', '-RTS'],
                                text=True, capture_output=True, cwd=ROOT, timeout=60)
        report = json.loads(result.stdout)
        failures = [d for d in report['diagnostics'] if d['code'] == 'partial-recursion']
        # Some declaration tutorials intentionally contain sort errors. This
        # census gates recursion acknowledgements, not those teaching fixtures.
        assert result.returncode in (0, 1), (path, result.stderr)
        errors = [d for d in report['diagnostics'] if d['severity'] == 'error']
        assert not errors or (path.name == 'v2_decls.nprolog'
                              and all(d['code'] == 'call-sort-mismatch' for d in errors)), (path, errors)
        assert not failures, (path, failures)
        count += len(report['predicates'])
    print(f'Recursion census: {len(files)} files, {count} predicate verdicts, no unacknowledged partial recursion')


if __name__ == '__main__':
    main()
