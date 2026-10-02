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
# setKey rewrites the root's record in place, so the counters show only the host's allocations
# of the argument's records.
for case in .:0 5,.,.:1 5,1,.,.,9,.,.:3; do
  tree=${case%:*}
  nodes=${case#*:}
  out=$("$host" call-stats "$build/treeMoves/treeMoves.wasm" setKey tree-u64 i64:7 "tree-u64:$tree" | tail -1)
  if [ "$out" != "stats $nodes 0" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: treeMoves setKey tree-u64:$tree: $out, expected stats $nodes 0"
  fi
done
echo "release counts: 19 cases, $stats_failed failed"
# The internal function of a recursive definition traps at `unreachable` at depth 1,000: a
# chain of 999 nodes succeeds, and a chain of 1,000 traps there, before Wasmtime's stack ends.
depth_failed=0
chain() { printf 'tree-u64:'; i=0; while [ "$i" -lt "$1" ]; do printf '1,.,'; i=$((i + 1)); done; printf '.'; }
out=$("$host" call "$build/trees/trees.wasm" size i64 "$(chain 999)" 2>&1) || true
if [ "$out" != "999" ]; then
  depth_failed=$((depth_failed + 1))
  echo "fail: trees size on a chain of 999: $out"
fi
out=$("$host" call "$build/trees/trees.wasm" size i64 "$(chain 1000)" 2>&1) || true
case "$out" in
  *"wasm \`unreachable\` instruction executed"*) ;;
  *) depth_failed=$((depth_failed + 1)); echo "fail: trees size on a chain of 1000: $out" ;;
esac
for module_name in trees:height treeFrame:wide; do
  module=${module_name%%:*}
  name=${module_name##*:}
  out=$("$host" call "$build/$module/$module.wasm" "$name" i64 "$(chain 999)" 2>&1) || true
  case "$out" in
    *trap*|*error*) depth_failed=$((depth_failed + 1)); echo "fail: $module $name on a chain of 999: $out" ;;
  esac
  out=$("$host" call "$build/$module/$module.wasm" "$name" i64 "$(chain 1000)" 2>&1) || true
  case "$out" in
    *"wasm \`unreachable\` instruction executed"*) ;;
    *) depth_failed=$((depth_failed + 1)); echo "fail: $module $name on a chain of 1000: $out" ;;
  esac
done
echo "depth guard: 6 cases, $depth_failed failed"
[ "$total" -gt 0 ] && [ "$failed" -eq 0 ] && [ "$stats_failed" -eq 0 ] && [ "$depth_failed" -eq 0 ]
