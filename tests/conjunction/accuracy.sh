#!/usr/bin/env bash
# The containment test of the circular and linear errors.  It builds the case executables, prints
# the results of Demos.Conjunction.Accuracy.circularError and linearError and of
# Demos.Conjunction.Adaptive.pcAdaptive and circularErrorAdaptive in native Lean for the inputs of
# tests/TestSupport/Conjunction/AccuracyCases.lean and AdaptiveCases.lean, and checks with
# tests/conjunction/accuracy.py that each reference, computed with mpmath, lies in its interval,
# and that the inputs whose search cannot finish return status 2.  It writes the results to
# build/conjunction/accuracy-cases.txt and the report, which also holds each interval's relative
# width, to build/conjunction/accuracy.txt.  With --sweep, it instead finds for each input of the
# sweep the least panel count at which each of circularError and circularErrorAdaptive returns
# status 0, checks the result at that count, and writes build/conjunction/sweep-cases.txt and the
# report build/conjunction/sweep.txt.
# Usage: tests/conjunction/accuracy.sh [--sweep]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/conjunction
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-accuracy \
  verified-cases-adaptive
if [ "${1:-}" = "--sweep" ]; then
  tools/leanrun --timeout 6h .lake/build/bin/verified-cases-adaptive --sweep >"$out/sweep-cases.txt"
  uv run tests/conjunction/accuracy.py "$out/sweep-cases.txt" | tee "$out/sweep.txt"
  exit 0
fi
tools/leanrun --timeout 60m .lake/build/bin/verified-cases-accuracy --bits >"$out/accuracy-cases.txt"
tools/leanrun --timeout 60m .lake/build/bin/verified-cases-adaptive --bits >>"$out/accuracy-cases.txt"
uv run tests/conjunction/accuracy.py "$out/accuracy-cases.txt" | tee "$out/accuracy.txt"
