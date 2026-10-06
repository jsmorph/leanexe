#!/usr/bin/env bash
# Runs build/drone/drone.wasm in the Wasmtime host on every call of tests/drone/cases.txt and on
# `compute` of every terrain of tests/drone/corpus.txt, and compares the results with the reference
# implementation's.  Usage: tests/drone/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
host=$root/build/tools/leanexe-wasmtime-host
total=0
failed=0
while IFS='|' read -r module name result args expected; do
  read -ra argv <<<"$args"
  total=$((total + 1))
  out=$("$host" call "$root/build/$module/$module.wasm" "$name" "$result" "${argv[@]}" |
    tr -d '[] ' | paste -sd, -)
  if [ "$out" != "$expected" ]; then
    failed=$((failed + 1))
    echo "fail: $name $args: $out, expected $expected"
  fi
done <"$root/tests/drone/cases.txt"
echo "drone calls in WebAssembly: $total cases, $failed failed"
calls_failed=$failed
total=0
failed=0
while IFS='|' read -r terrain expected; do
  total=$((total + 1))
  out=$("$host" call "$root/build/drone/drone.wasm" compute array-u64 "array-u64:$terrain" |
    tr -d '[] ' | paste -sd, -)
  if [ "$out" != "$expected" ]; then
    failed=$((failed + 1))
    echo "fail: $terrain: $out, expected $expected"
  fi
done <"$root/tests/drone/corpus.txt"
echo "drone corpus in WebAssembly: $total cases, $failed failed"
[ "$calls_failed" -eq 0 ] && [ "$failed" -eq 0 ]
