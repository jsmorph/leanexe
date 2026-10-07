#!/usr/bin/env bash
# Writes the modules of the verified compiler's examples, validates them with wasm-tools, and
# compares every case of Verified/Examples/Cases.lean between the Wasmtime host and native Lean.
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
    Verified.Examples.Loops:compiled.module:loops; do
  IFS=: read -r module constant name <<<"$entry"
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$module" "$module.$constant" \
    "$out/$name.wasm"
  wasm-tools validate "$out/$name.wasm"
done
cases=$(mktemp)
trap 'rm -f "$cases"' EXIT
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/Cases.lean >"$cases"
passed=0
failed=0
while IFS='|' read -r name export result args expected; do
  read -ra argv <<<"$args"
  got=$("$host" call "$out/$name.wasm" "$export" "$result" "${argv[@]}" | paste -sd' ')
  if [ "$got" = "$expected" ]; then
    passed=$((passed + 1))
  else
    failed=$((failed + 1))
    echo "fail: $name $export $args: $got, expected $expected"
  fi
done <"$cases"
echo "verified: passed $passed failed $failed"
[ "$passed" -gt 0 ] && [ "$failed" -eq 0 ]
