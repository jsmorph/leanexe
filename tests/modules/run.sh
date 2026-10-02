#!/usr/bin/env bash
# Compares every case of tests/modules/Cases.lean between the Wasmtime host running
# build/MODULE/MODULE.wasm and native Lean.  Usage: tests/modules/run.sh [build directory]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
build=${1:-$root/build}
host=$root/build/tools/leanexe-wasmtime-host
cases=$(mktemp)
trap 'rm -f "$cases"' EXIT
# Out-of-bounds reads with `!` print panic messages from native Lean; they are expected.
(cd "$root" && tools/leanrun --timeout 10m lake env lean --run tests/modules/Cases.lean) >"$cases" 2>/dev/null
declare -A passed
failed=0
while IFS='|' read -r module name result args expected; do
  read -ra argv <<<"$args"
  out=$("$host" call "$build/$module/$module.wasm" "$name" "$result" "${argv[@]}" | tr -d '[] ' | paste -sd, -)
  if [ "$out" = "$expected" ]; then
    passed[$module.$name]=$((${passed[$module.$name]:-0} + 1))
  else
    failed=$((failed + 1))
    echo "fail: $module $name $args: $out, expected $expected"
  fi
done <"$cases"
total=0
for name in $(printf '%s\n' "${!passed[@]}" | sort); do
  echo "$name ${passed[$name]}"
  total=$((total + ${passed[$name]}))
done
echo "passed $total failed $failed"
# The CLOB functions that consume their arrays release them inside the call on the paths that
# do not return them.  The host releases nothing, so the counters show those frees.  Each line
# is an export, its arguments, and the expected allocations and frees.
stats_failed=0
prices=array-u64:105,102,101
sizes=array-u64:4,4,6
while IFS='|' read -r name args expected; do
  read -ra argv <<<"$args"
  out=$("$host" call-stats "$build/clob/clob.wasm" "$name" list:array-u64,array-u64 \
    $prices $sizes "${argv[@]}" | tail -1)
  if [ "$out" != "stats $expected" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: clob $name $args: $out, expected stats $expected"
  fi
done <<'CASES'
setLevel|i64:1 i64:9|3 0
addBid|i64:103 i64:5|4 1
addBid|i64:102 i64:5|3 0
cancelBid|i64:102 i64:4|4 2
cancelBid|i64:102 i64:1|3 1
cancelBid|i64:103 i64:1|2 0
applyCommand|i64:0 i64:103 i64:5|4 2
applyCommand|i64:0 i64:102 i64:5|3 1
applyCommand|i64:1 i64:102 i64:4|4 2
applyCommand|i64:1 i64:102 i64:1|3 1
applyCommand|i64:2 i64:102 i64:1|2 0
CASES
# sumRange releases the list of n cells that it builds, so the counters show n allocations and
# n frees.
for n in 0 1 2 64 300; do
  out=$("$host" call-stats "$build/lists/lists.wasm" sumRange i64 "i64:$n" | tail -1)
  if [ "$out" != "stats $n $n" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: lists sumRange i64:$n: $out, expected stats $n $n"
  fi
done
echo "release counts: 16 cases, $stats_failed failed"
[ "$total" -gt 0 ] && [ "$failed" -eq 0 ] && [ "$stats_failed" -eq 0 ]
