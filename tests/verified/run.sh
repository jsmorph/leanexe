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
for entry in Verified.Examples.Poly:poly Verified.Examples.Mix:mix \
    Verified.Examples.Lets:lets; do
  IFS=: read -r module name <<<"$entry"
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$module" "$module.module" \
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
  got=$("$host" call "$out/$name.wasm" "$export" "$result" "${argv[@]}")
  if [ "$got" = "$expected" ]; then
    passed=$((passed + 1))
  else
    failed=$((failed + 1))
    echo "fail: $name $export $args: $got, expected $expected"
  fi
done <"$cases"
echo "verified: passed $passed failed $failed"
[ "$passed" -gt 0 ] && [ "$failed" -eq 0 ]
