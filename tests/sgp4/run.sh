#!/usr/bin/env bash
# The reference test of the SGP4 programs.  It builds the case executables and compares
# Demos.Sgp4.sgp4 and Demos.Sgp4.sgp4BoxAround in native Lean with the reference states of
# tests/sgp4/near-earth.out, by tests/sgp4/reference.py.  It writes the report to
# build/sgp4/reference.txt.
# Usage: tests/sgp4/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/sgp4
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-sgp4 verified-cases-sgp4box
uv run tests/sgp4/reference.py .lake/build/bin/verified-cases-sgp4 \
  .lake/build/bin/verified-cases-sgp4box | tee "$out/reference.txt"
