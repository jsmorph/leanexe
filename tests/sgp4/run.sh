#!/usr/bin/env bash
# The reference test of the SGP4 program.  It builds the case executable and compares
# Demos.Sgp4.sgp4 in native Lean with the reference states of tests/sgp4/near-earth.out, by
# tests/sgp4/reference.py.  It writes the report to build/sgp4/reference.txt.
# Usage: tests/sgp4/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/sgp4
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-sgp4
uv run tests/sgp4/reference.py .lake/build/bin/verified-cases-sgp4 | tee "$out/reference.txt"
