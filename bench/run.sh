#!/bin/sh
# Validated engine benchmarks; all process execution and timing is in Python.
set -eu
exec python3 "$(dirname "$0")/run.py" "$@"
