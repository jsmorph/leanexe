#!/usr/bin/env bash
# Writes the modules of the verified compiler's examples, validates them with wasm-tools, and
# compares every case of Verified/Examples/Cases.lean between the Wasmtime host and native Lean.
# A case with a sixth field also checks the allocation counters: the blocks allocated less those
# released must equal the field, the host's array arguments and the result's arrays.  A seventh
# field bounds the number of allocations, the host's included.  A case whose expected result is
# `trap` must trap at `unreachable`.
# Run `tools/leanrun --timeout 60m lake build Verified` first.  Usage: tests/verified/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
host=$root/build/tools/leanexe-wasmtime-host
out=$root/build/verified
mkdir -p "$out"
cd "$root"
for entry in Verified.Examples.Poly:compiled.module:poly Verified.Examples.Mix:compiled.module:mix \
    Verified.Examples.Lets:compiled.module:lets Verified.Examples.Select:compiled.module:select \
    Verified.Examples.Calls:compiled.module:calls Verified.Examples.Pairs:compiled.module:pairs \
    Verified.Examples.Loops:compiled.module:loops \
    Verified.Examples.Arrays:compiled.module:arrays \
    Verified.Examples.Owned:compiled.module:owned \
    Verified.Examples.Updates:compiled.module:updates \
    Verified.Examples.Grow:compiled.module:grow \
    Verified.Examples.Modes:compiled.module:modes \
    Verified.Examples.Modes:byHandModule:byhand; do
  IFS=: read -r module constant name <<<"$entry"
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$module" "$module.$constant" \
    "$out/$name.wasm"
  wasm-tools validate "$out/$name.wasm"
done
cases=$(mktemp)
errors=$(mktemp)
trap 'rm -f "$cases" "$errors"' EXIT
# Native Lean panics on the reads and updates past the end of an array that the cases exercise: it
# writes a message and a backtrace to standard error, and a read returns Lean's default value and
# an update the array unchanged.  The run fails when Lean exits with an error or writes any other
# message.
if ! tools/leanrun --timeout 10m lake env lean --run Verified/Examples/Cases.lean \
    >"$cases" 2>"$errors"; then
  cat "$errors" >&2
  echo "fail: native Lean exited with an error" >&2
  exit 1
fi
counts=$(awk '
  $0 == "Error: index out of bounds" { reads++; next }
  $0 == "backtrace:" || /\[0x[0-9a-f]+\]$/ { next }
  { others++; print > "/dev/stderr" }
  END { print reads + 0, others + 0 }' "$errors")
read -r reads others <<<"$counts"
if [ "$others" -ne 0 ]; then
  echo "fail: native Lean wrote $others unexpected lines to standard error, shown above" >&2
  exit 1
fi
echo "native Lean: $reads accesses past the end, as the cases expect"
passed=0
failed=0
while IFS='|' read -r name export result args expected live allocsMax; do
  read -ra argv <<<"$args"
  if [ "$expected" = "trap" ]; then
    if "$host" call "$out/$name.wasm" "$export" "$result" "${argv[@]}" >/dev/null 2>"$errors"; then
      failed=$((failed + 1))
      echo "fail: $name $export $args: returned, expected a trap at unreachable"
    elif grep -q 'wasm `unreachable` instruction executed' "$errors"; then
      passed=$((passed + 1))
    else
      failed=$((failed + 1))
      echo "fail: $name $export $args: $(cat "$errors"), expected a trap at unreachable"
    fi
    continue
  fi
  if [ -z "$live" ]; then
    got=$("$host" call "$out/$name.wasm" "$export" "$result" "${argv[@]}" | paste -sd' ')
    held=""
  else
    output=$("$host" call-stats "$out/$name.wasm" "$export" "$result" "${argv[@]}")
    got=$(sed '$d' <<<"$output" | paste -sd' ')
    read -r _ allocs frees < <(tail -n 1 <<<"$output")
    held=$((allocs - frees))
  fi
  if [ -n "$allocsMax" ] && [ "$allocs" -gt "$allocsMax" ]; then
    failed=$((failed + 1))
    echo "fail: $name $export $args: $allocs allocations, at most $allocsMax expected"
  elif [ "$got" = "$expected" ] && [ "$held" = "$live" ]; then
    passed=$((passed + 1))
  else
    failed=$((failed + 1))
    echo "fail: $name $export $args: $got, expected $expected; live blocks $held, expected $live"
  fi
done <"$cases"
echo "verified: passed $passed failed $failed"
[ "$passed" -gt 0 ] && [ "$failed" -eq 0 ]
