#!/usr/bin/env bash
# The oracle test of the assignment check.  It builds the case executable, prints the results of
# Demos.Gate.Assignment.check in native Lean for the certificates of the unproved solver in
# tests/TestSupport/Gate/AssignmentCases.lean and their mutations, and checks them with
# tests/gate/assignment.py against a model of the check and the least cost of each instance.  It
# writes the results to build/gate/assignment-cases.txt and the report to build/gate/assignment.txt.
# Usage: tests/gate/assignment.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/gate
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-assignment
tools/leanrun --timeout 60m .lake/build/bin/verified-cases-assignment --bits >"$out/assignment-cases.txt"
uv run tests/gate/assignment.py "$out/assignment-cases.txt" | tee "$out/assignment.txt"
