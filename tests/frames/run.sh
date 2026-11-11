#!/usr/bin/env bash
# The containment test of the frames programs.  It builds the case executable, writes the input
# lines of tests/frames/oracle.py, runs them through the executable's --serve mode in native Lean,
# and checks every result against the oracle.  It writes the inputs, the results, and the report to
# build/frames.
# Usage: tests/frames/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/frames
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-frames
uv run tests/frames/oracle.py inputs >"$out/inputs.txt"
tools/leanrun --timeout 60m .lake/build/bin/verified-cases-frames --serve \
  <"$out/inputs.txt" >"$out/results.txt"
uv run tests/frames/oracle.py check "$out/results.txt" | tee "$out/report.txt"
