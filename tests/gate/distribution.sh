#!/usr/bin/env bash
# The oracle test of the chi-square programs.  It builds the case executable, prints the results
# of Demos.Gate.tail, cdf, and quantile in native Lean for the inputs of
# tests/TestSupport/Gate/ChiSquareCases.lean, and checks with tests/gate/distribution.py that each
# reference value, computed with mpmath, lies in its interval.  It writes the results to
# build/gate/distribution-cases.txt and the report to build/gate/distribution.txt.
# Usage: tests/gate/distribution.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/gate
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-chisquare
tools/leanrun --timeout 60m .lake/build/bin/verified-cases-chisquare --bits >"$out/distribution-cases.txt"
uv run tests/gate/distribution.py "$out/distribution-cases.txt" | tee "$out/distribution.txt"
