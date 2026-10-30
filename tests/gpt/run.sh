#!/usr/bin/env bash
# Compares every case of tests/gpt/Cases.lean between the Wasmtime host running
# gpt.wasm and native Lean.  The module is build/verified/gpt.wasm, which
# tests/verified/run.sh writes, unless a path is given, such as build/gpt/gpt.wasm for the
# LeanExe compiler's module.  Usage: tests/gpt/run.sh [path/to/gpt.wasm]
set -euo pipefail
if [ "$#" -gt 1 ]; then
  echo "usage: tests/gpt/run.sh [path/to/gpt.wasm]" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
wasm=${1:-$root/build/verified/gpt.wasm}
host=$root/build/tools/leanexe-wasmtime-host
if [ ! -x "$host" ] || [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  echo "fail: $host is missing or older than tools/wasmtime-host.c; build it with tools/build-wasmtime-host.sh" >&2
  exit 1
fi
cases=$(mktemp)
errors=$(mktemp)
trap 'rm -f "$cases" "$errors"' EXIT
if ! (cd "$root" && tools/leanrun --timeout 10m lake env lean --run tests/gpt/Cases.lean) \
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
declare -A passed
failed=0
while IFS='|' read -r name result args expected; do
  read -ra argv <<<"$args"
  out=$("$host" call "$wasm" "$name" "$result" "${argv[@]}" | tr -d '[] ' | paste -sd, -)
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
