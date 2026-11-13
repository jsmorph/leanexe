#!/usr/bin/env bash
# The comparison of the conjunction program with the two-dimensional unit tests of NASA's CARA
# Analysis Tools.  It downloads the tests' files at the commit that tests/conjunction/cara.py pins
# into build/conjunction/cara and checks their sizes and SHA-256, builds verified-cases-adaptive,
# writes the encounter-plane inputs of the cases, evaluates Demos.Conjunction.pc and pcAdaptive on
# them in native Lean, and checks each result and each of CARA's values with cara.py.  It writes
# the inputs, the results, and the report to build/conjunction.
# Usage: tests/conjunction/cara.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/conjunction
data=$out/cara
mkdir -p "$data"
uv run tests/conjunction/cara.py fetch "$data"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-adaptive
uv run tests/conjunction/cara.py inputs "$data" >"$out/cara-inputs.txt"
tools/leanrun --timeout 60m .lake/build/bin/verified-cases-adaptive \
  --evaluate "$out/cara-inputs.txt" >"$out/cara-results.txt"
uv run tests/conjunction/cara.py check "$data" "$out/cara-results.txt" | tee "$out/cara.txt"
