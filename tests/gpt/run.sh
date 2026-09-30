#!/usr/bin/env bash
# Compares every case of tests/gpt/Cases.lean between the Wasmtime host running
# gpt.wasm and native Lean.  Usage: tests/gpt/run.sh [path/to/gpt.wasm]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
wasm=${1:-$root/build/gpt/gpt.wasm}
host=$root/build/tools/leanexe-wasmtime-host
cases=$(mktemp)
trap 'rm -f "$cases"' EXIT
# Out-of-bounds reads with `!` print panic messages from native Lean; they are expected.
(cd "$root" && tools/leanrun --timeout 10m lake env lean --run tests/gpt/Cases.lean) >"$cases" 2>/dev/null
declare -A passed
failed=0
while IFS='|' read -r name result args expected; do
  read -ra argv <<<"$args"
  out=$("$host" call "$wasm" "$name" "$result" "${argv[@]}" | tr -d '[] ')
  if [ "$out" = "$expected" ]; then
    passed[$name]=$((${passed[$name]:-0} + 1))
  else
    failed=$((failed + 1))
    echo "fail: $name"
  fi
done <"$cases"
total=0
for name in $(printf '%s\n' "${!passed[@]}" | sort); do
  echo "$name ${passed[$name]}"
  total=$((total + ${passed[$name]}))
done
echo "passed $total failed $failed"
[ "$total" -gt 0 ] && [ "$failed" -eq 0 ]
