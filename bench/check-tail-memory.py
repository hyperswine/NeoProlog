#!/usr/bin/env python3
"""Check bounded tail residency in fresh processes, including disabled tracing.

Build with cabal build bench:machine-tail --enable-optimization=2, then run:
python3 bench/check-tail-memory.py BINARY --output samples.jsonl [--quick]
The quick CI gate checks mutual recursion and helpers; the full gate adds live checkpoints,
structured arguments, helpers, CLP, tables and dynamic state. Timings are reports.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def source_hash():
    digest = hashlib.sha256()
    for path in sorted((ROOT / "src").rglob("*.hs")):
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0" + path.read_bytes() + b"\0")
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    binary = str(args.binary.resolve())
    if sys.platform == "darwin":
        timer, peak_pattern, unit = ["/usr/bin/time", "-l"], r"(\d+)\s+maximum resident set size", 1
    elif sys.platform.startswith("linux"):
        timer, peak_pattern, unit = ["/usr/bin/time", "-v"], r"Maximum resident set size \(kbytes\):\s*(\d+)", 1024
    else:
        parser.error("fresh-process RSS collection currently supports macOS and Linux")
    matrix = []
    for case in (["mutual"] if args.quick else ["mutual", "choice", "findall"]):
        matrix.extend((case, count, False, 1) for count in [10000, 100000])
        matrix.extend((case, 1000000, False, repeat) for repeat in range(1, 2 if args.quick else 4))
        matrix.append((case, 1000000, True, 1))
    for case in (["helper"] if args.quick else ["helper", "structured", "clp", "cached", "dynamic"]):
        matrix.extend((case, 1000000, measured, 1) for measured in [False, True])
    fingerprint = source_hash()
    prefix_rss = prefix_live = 0
    with args.output.open("w") as destination:
        for case, count, measured, repeat in matrix:
            command = timer + [binary, str(count), "--case", case]
            if not measured:
                command.append("--unmeasured")
            command += ["+RTS", "-T", "-s", "-RTS"]
            result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True,
                                    timeout=180, check=True)
            row = json.loads(result.stdout)
            peak = re.search(peak_pattern, result.stderr)
            if peak is None:
                raise RuntimeError("Missing process peak RSS: " + result.stderr)
            rss = int(peak.group(1)) * unit
            live = row["process_max_live_bytes"]
            if count < 1000000:
                prefix_rss, prefix_live = max(prefix_rss, rss), max(prefix_live, live)
            passed = rss <= 1.5 * prefix_rss and live <= 1.5 * prefix_live
            row.update(peak_rss_bytes=rss, repeat=repeat, runtime_source_sha256=fingerprint,
                       build_profile="Cabal --enable-optimization=2; runner -O2",
                       process_command=command,
                       residency_policy="RSS and RTS maximum live bytes <= 1.5x prefix maxima",
                       residency_check_passed=passed)
            destination.write(json.dumps(row) + "\n")
            destination.flush()
            print(case, count, "measured" if measured else "normal", repeat,
                  round(row["wall_seconds"], 3), rss, flush=True)
            if not passed:
                raise RuntimeError("Tail residency grew beyond the prefix bound; sample retained")
    if source_hash() != fingerprint:
        raise RuntimeError("Runtime sources changed during measurements")
    print("Tail residency gate passed", flush=True)


if __name__ == "__main__":
    main()
