#!/usr/bin/env bash
# The containment test of the circular and linear errors.  It builds the case executable, prints
# the results of Demos.Conjunction.Accuracy.circularError and linearError in native Lean for the
# inputs of tests/TestSupport/Conjunction/AccuracyCases.lean, and checks with
# tests/conjunction/accuracy.py that each reference radius, computed with mpmath, lies in its
# interval, and that the inputs whose search cannot finish return status 2.  It writes the results
# to build/conjunction/accuracy-cases.txt and the report, which also holds each interval's
# relative width, to build/conjunction/accuracy.txt.
# Usage: tests/conjunction/accuracy.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/conjunction
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-accuracy
tools/leanrun --timeout 60m .lake/build/bin/verified-cases-accuracy --bits >"$out/accuracy-cases.txt"
uv run tests/conjunction/accuracy.py "$out/accuracy-cases.txt" | tee "$out/accuracy.txt"
