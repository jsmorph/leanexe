#!/usr/bin/env bash
# The oracle test of the gate.  It builds the case executable, prints the results of
# Demos.Gate.gate in native Lean for the inputs of tests/TestSupport/Gate/GateCases.lean, and checks
# with tests/gate/gate.py that each accepted interval contains the squared Mahalanobis distance,
# computed with exact rationals and mpmath, that each verdict follows its rule, and that the
# statuses agree with the reference's decision of positive definiteness.  It writes the results to
# build/gate/gate-cases.txt and the report to build/gate/gate.txt.
# Usage: tests/gate/gate.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/gate
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-gate
tools/leanrun --timeout 60m .lake/build/bin/verified-cases-gate --bits >"$out/gate-cases.txt"
uv run tests/gate/gate.py "$out/gate-cases.txt" | tee "$out/gate.txt"
