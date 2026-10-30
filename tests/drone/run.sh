#!/usr/bin/env bash
# Runs a drone module in the Wasmtime host on every call of tests/drone/cases.txt and on `compute` of
# every terrain of tests/drone/corpus.txt, and compares the results with the reference
# implementation's.  The module is build/verified/drone.wasm, which tests/verified/run.sh writes,
# unless a path is given, such as build/drone/drone.wasm for the LeanExe compiler's module.
# Usage: tests/drone/run.sh [path/to/drone.wasm]
set -euo pipefail
if [ "$#" -gt 1 ]; then
  echo "usage: tests/drone/run.sh [path/to/drone.wasm]" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
wasm=${1:-$root/build/verified/drone.wasm}
host=$root/build/tools/leanexe-wasmtime-host
if [ ! -x "$host" ] || [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  echo "fail: $host is missing or older than tools/wasmtime-host.c; build it with tools/build-wasmtime-host.sh" >&2
  exit 1
fi
total=0
failed=0
while IFS='|' read -r _ name result args expected; do
  read -ra argv <<<"$args"
  total=$((total + 1))
  out=$("$host" call "$wasm" "$name" "$result" "${argv[@]}" |
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
  out=$("$host" call "$wasm" compute array-u64 "array-u64:$terrain" |
    tr -d '[] ' | paste -sd, -)
  if [ "$out" != "$expected" ]; then
    failed=$((failed + 1))
    echo "fail: $terrain: $out, expected $expected"
  fi
done <"$root/tests/drone/corpus.txt"
echo "drone corpus in WebAssembly: $total cases, $failed failed"
[ "$calls_failed" -eq 0 ] && [ "$failed" -eq 0 ]
