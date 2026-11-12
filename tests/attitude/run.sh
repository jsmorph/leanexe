#!/usr/bin/env bash
# The containment and bound test of the attitude program.  It builds the case executable, prints
# the results of Demos.Attitude.triad in native Lean for the cases of
# tests/TestSupport/Attitude/Cases.lean, and checks them with tests/attitude/reference.py, which
# computes TRIAD and its error bound in mpmath at 50 digits.  It writes the report to
# build/attitude/reference.txt.
# Usage: tests/attitude/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/attitude
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-attitude
.lake/build/bin/verified-cases-attitude --bits >"$out/cases.txt"
uv run tests/attitude/reference.py "$out/cases.txt" | tee "$out/reference.txt"
