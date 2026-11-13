#!/usr/bin/env bash
# The differential test of the conjunction program against published cases.  It builds
# conjunction-evaluate, writes the encounter-plane inputs of tests/conjunction/published.py with
# tests/conjunction/benchmark.py, evaluates Demos.Conjunction.pc and pcAdaptive on them in native
# Lean, and checks each result against the reference of tests/conjunction/reference.py and each
# published value.  It writes the inputs, the results, and the report to build/conjunction.
# Usage: tests/conjunction/benchmark.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/conjunction
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build conjunction-evaluate
uv run tests/conjunction/benchmark.py inputs >"$out/benchmark-inputs.txt"
tools/leanrun --timeout 60m .lake/build/bin/conjunction-evaluate "$out/benchmark-inputs.txt" \
  >"$out/benchmark-results.txt"
uv run tests/conjunction/benchmark.py check "$out/benchmark-results.txt" | tee "$out/benchmark.txt"
