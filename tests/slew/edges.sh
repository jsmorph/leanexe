#!/usr/bin/env bash
# Compares the edgeOk export of slew.wasm with native Lean on the 100,000 single-cone edges of
# tests/TestSupport/Slew/Edges.lean, all in one host session, and checks that the session releases
# every block it allocates.
# Usage: tests/slew/edges.sh [path/to/slew.wasm]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
wasm=${1:-$root/build/verified/slew.wasm}
host=$root/build/tools/leanexe-wasmtime-host
cd "$root"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
tools/leanrun --timeout 30m lake --log-level error build TestSupport.Slew.EdgesMain
tools/leanrun --timeout 30m lake env lean --run tests/TestSupport/Slew/EdgesMain.lean \
  "$dir/script" "$dir/expected"
"$host" session "$wasm" <"$dir/script" >"$dir/output"
grep -E '^results [01]$' "$dir/output" >"$dir/got" || true
if ! cmp -s "$dir/got" "$dir/expected"; then
  diff "$dir/got" "$dir/expected" | head -20 || true
  echo "fail: slew edges: the module's edgeOk differs from native Lean at the lines shown" >&2
  exit 1
fi
read -r _ allocs frees < <(tail -n 1 "$dir/output")
if [ "$allocs" != "$frees" ]; then
  echo "fail: slew edges: $allocs allocations, $frees frees" >&2
  exit 1
fi
echo "slew edges: $(wc -l <"$dir/expected") edges agree with native Lean, $allocs allocations, $frees frees"
