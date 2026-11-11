#!/usr/bin/env bash
# The oracle test of the q-method.  It builds the case executable, prints the results of
# Demos.Attitude.QMethod.qmethod in native Lean for the cases of
# tests/TestSupport/Attitude/QCases.lean, and checks them with tests/attitude/qreference.py, which
# computes Davenport's matrix, its eigenvectors, and the q-method's bounds in mpmath at 50 digits.
# It writes the report to build/attitude/qreference.txt.
# Usage: tests/attitude/qrun.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/attitude
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-qmethod
.lake/build/bin/verified-cases-qmethod --bits >"$out/qcases.txt"
uv run tests/attitude/qreference.py "$out/qcases.txt" | tee "$out/qreference.txt"
