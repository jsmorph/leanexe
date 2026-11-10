#!/usr/bin/env bash
# The containment test of the conjunction program.  It builds the case executable, prints the
# intervals of Demos.Conjunction.pc in native Lean for the valid inputs of
# tests/TestSupport/Conjunction/Cases.lean at 16, 256, and 4,096 panels, and checks with
# tests/conjunction/reference.py that a reference value of the probability, integrated over the
# disk with mpmath at 50 digits, lies in each interval.  It writes the report, which also holds
# each interval's width, to build/conjunction/reference.txt.
# Usage: tests/conjunction/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/conjunction
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-conjunction
.lake/build/bin/verified-cases-conjunction --bits >"$out/cases.txt"
uv run tests/conjunction/reference.py "$out/cases.txt" | tee "$out/reference.txt"
