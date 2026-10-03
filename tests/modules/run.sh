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
setLevel|i64:1 i64:9|2 0
addBid|i64:103 i64:5|4 2
addBid|i64:102 i64:5|2 0
cancelBid|i64:102 i64:4|2 0
cancelBid|i64:102 i64:1|2 0
cancelBid|i64:103 i64:1|2 0
applyCommand|i64:0 i64:103 i64:5|4 2
applyCommand|i64:0 i64:102 i64:5|2 0
applyCommand|i64:1 i64:102 i64:4|2 0
applyCommand|i64:1 i64:102 i64:1|2 0
applyCommand|i64:2 i64:102 i64:1|2 0
CASES
# Two inserts in one call: the first moves each array to a block of twice the capacity and
# releases the old block, and the second fits, so the counters show 3 host allocations, 2 more
# blocks, and 2 frees.
out=$("$host" call-stats "$build/clob/clob.wasm" runCommands list:array-u64,array-u64 \
  $prices $sizes array-u64:0,103,5,0,104,5 | tail -1)
if [ "$out" != "stats 5 2" ]; then
  stats_failed=$((stats_failed + 1))
  echo "fail: clob runCommands with two inserts: $out, expected stats 5 2"
fi
# stepCommand pushes two words onto the output array in place.  An output of one word fills its
# block, so the first push moves it to a block of twice the capacity and the second fits: 3 host
# allocations, 1 more block, and 1 free.  An empty output grows on both pushes.
for case in "array-u64:7|4 1" "array-u64:|5 2"; do
  IFS='|' read -r output expected <<<"$case"
  out=$("$host" call-stats "$build/clob/clob.wasm" stepCommand \
    list:array-u64,array-u64,array-u64 $prices $sizes "$output" i64:1 i64:102 i64:4 | tail -1)
  if [ "$out" != "stats $expected" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: clob stepCommand with output $output: $out, expected stats $expected"
  fi
done
# sumRange releases the list of n cells that it builds, so the counters show n allocations and
# n frees.
for n in 0 1 2 64 300; do
  out=$("$host" call-stats "$build/lists/lists.wasm" sumRange i64 "i64:$n" | tail -1)
  if [ "$out" != "stats $n $n" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: lists sumRange i64:$n: $out, expected stats $n $n"
  fi
done
# setKey and incr rewrite the argument's records in place, so the counters show only the host's
# allocations of those records.
for case in .:0 5,.,.:1 5,1,.,.,9,.,.:3; do
  tree=${case%:*}
  nodes=${case#*:}
  for call in "setKey i64:7" incr; do
    read -ra argv <<<"$call"
    out=$("$host" call-stats "$build/treeMoves/treeMoves.wasm" "${argv[0]}" tree-u64 \
      "${argv[@]:1}" "tree-u64:$tree" | tail -1)
    if [ "$out" != "stats $nodes 0" ]; then
      stats_failed=$((stats_failed + 1))
      echo "fail: treeMoves $call tree-u64:$tree: $out, expected stats $nodes 0"
    fi
  done
done
# insert allocates one record for a new key and none for a key already present.
for case in "i64:7 .:1 0" "i64:7 5,.,.:2 0" "i64:7 5,1,.,.,9,.,.:4 0" "i64:5 5,1,.,.,9,.,.:3 0" \
    "i64:9 5,1,.,.,9,.,.:3 0"; do
  read -r key rest <<<"$case"
  tree=${rest%%:*}
  expected=${rest#*:}
  out=$("$host" call-stats "$build/treeMoves/treeMoves.wasm" insert tree-u64 "$key" \
    "tree-u64:$tree" | tail -1)
  if [ "$out" != "stats $expected" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: treeMoves insert $key tree-u64:$tree: $out, expected stats $expected"
  fi
done
# dropRight frees the right subtree's records, and leftChild frees the root's record and the
# right subtree's.  Each case is a tree, then the expected counts for dropRight and leftChild.
for case in ".|0 0|0 0" "5,.,.|1 0|1 1" "5,1,.,.,9,.,.|3 1|3 2" "5,1,.,.,9,7,.,.,8,.,.|5 3|5 4"; do
  IFS='|' read -r tree drop left <<<"$case"
  for call in "dropRight:$drop" "leftChild:$left"; do
    name=${call%%:*}
    expected=${call#*:}
    out=$("$host" call-stats "$build/treeMoves/treeMoves.wasm" "$name" tree-u64 \
      "tree-u64:$tree" | tail -1)
    if [ "$out" != "stats $expected" ]; then
      stats_failed=$((stats_failed + 1))
      echo "fail: treeMoves $name tree-u64:$tree: $out, expected stats $expected"
    fi
  done
done
# keepIf with c other than 0 frees every record.  trim frees what leftChild frees when the
# root's key is 0, and what dropRight frees otherwise.
for case in "keepIf i64:0|5,1,.,.,9,.,.|3 0" "keepIf i64:1|5,1,.,.,9,.,.|3 3" "keepIf i64:1|.|0 0" \
    "trim|0,1,.,.,9,.,.|3 2" "trim|5,1,.,.,9,.,.|3 1" "trim|.|0 0"; do
  IFS='|' read -r call tree expected <<<"$case"
  read -ra argv <<<"$call"
  out=$("$host" call-stats "$build/treeMoves/treeMoves.wasm" "${argv[0]}" tree-u64 \
    "${argv[@]:1}" "tree-u64:$tree" | tail -1)
  if [ "$out" != "stats $expected" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: treeMoves $call tree-u64:$tree: $out, expected stats $expected"
  fi
done
# insertTwo calls insert twice on the same records: two new keys add two records, and two keys
# already present add none.
for case in "i64:7 i64:8|5 0" "i64:5 i64:9|3 0"; do
  IFS='|' read -r keys expected <<<"$case"
  read -ra argv <<<"$keys"
  out=$("$host" call-stats "$build/treeMoves/treeMoves.wasm" insertTwo tree-u64 "${argv[@]}" \
    "tree-u64:5,1,.,.,9,.,." | tail -1)
  if [ "$out" != "stats $expected" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: treeMoves insertTwo $keys: $out, expected stats $expected"
  fi
done
# pushSum grows the host's exact-capacity array once, freeing the old block, and reads the tree
# without allocating: the host's array and records, then one block.
for case in "array-u64:7|5,1,.,.,9,.,.|5 1" "array-u64:|.|2 1"; do
  IFS='|' read -r xs tree expected <<<"$case"
  out=$("$host" call-stats "$build/trees/trees.wasm" pushSum list:array-u64,i64 "$xs" \
    "tree-u64:$tree" | tail -1)
  if [ "$out" != "stats $expected" ]; then
    stats_failed=$((stats_failed + 1))
    echo "fail: trees pushSum $xs tree-u64:$tree: $out, expected stats $expected"
  fi
done
echo "release counts: 48 cases, $stats_failed failed"
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
for module_name in trees:height:i64 treeFrame:wide:i64 treeMoves:incr:tree-u64; do
  IFS=: read -r module name kind <<<"$module_name"
  out=$("$host" call "$build/$module/$module.wasm" "$name" "$kind" "$(chain 999)" 2>&1) || true
  case "$out" in
    *trap*|*error*) depth_failed=$((depth_failed + 1)); echo "fail: $module $name on a chain of 999: $out" ;;
  esac
  out=$("$host" call "$build/$module/$module.wasm" "$name" "$kind" "$(chain 1000)" 2>&1) || true
  case "$out" in
    *"wasm \`unreachable\` instruction executed"*) ;;
    *) depth_failed=$((depth_failed + 1)); echo "fail: $module $name on a chain of 1000: $out" ;;
  esac
done
# insert of a key larger than every key of a chain recurses to its end.
out=$("$host" call "$build/treeMoves/treeMoves.wasm" insert tree-u64 i64:2 "$(chain 999)" 2>&1) || true
case "$out" in
  *trap*|*error*) depth_failed=$((depth_failed + 1)); echo "fail: treeMoves insert on a chain of 999: $out" ;;
esac
out=$("$host" call "$build/treeMoves/treeMoves.wasm" insert tree-u64 i64:2 "$(chain 1000)" 2>&1) || true
case "$out" in
  *"wasm \`unreachable\` instruction executed"*) ;;
  *) depth_failed=$((depth_failed + 1)); echo "fail: treeMoves insert on a chain of 1000: $out" ;;
esac
# Releasing a long chain: dropRight on a chain of 999 nodes frees the 998 records of its right
# subtree, and leftChild frees all 999.
for call in "dropRight:999 998" "leftChild:999 999"; do
  name=${call%%:*}
  expected=${call#*:}
  out=$("$host" call-stats "$build/treeMoves/treeMoves.wasm" "$name" tree-u64 "$(chain 999)" 2>&1 | tail -1) || true
  if [ "$out" != "stats $expected" ]; then
    depth_failed=$((depth_failed + 1))
    echo "fail: treeMoves $name on a chain of 999: $out, expected stats $expected"
  fi
done
echo "depth guard: 12 cases, $depth_failed failed"
[ "$total" -gt 0 ] && [ "$failed" -eq 0 ] && [ "$stats_failed" -eq 0 ] && [ "$depth_failed" -eq 0 ]
