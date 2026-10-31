#!/usr/bin/env bash
# Compares the cases of module NAME in tests/TestSupport/Native/ModuleCases.lean between the
# Wasmtime host running WASM and native Lean.  tests/verified/run.sh runs it on the verified euler
# module and, under the name shapes, on the verified sums module.
# Usage: tests/modules/run.sh --module NAME WASM
set -euo pipefail
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"
root=$(cd "$(dirname "$0")/../.." && pwd)
if [ "$#" -ne 3 ] || [ "$1" != "--module" ] || [ -z "$2" ] || [ -z "$3" ]; then
  echo "usage: tests/modules/run.sh --module NAME WASM" >&2
  exit 2
fi
case_module=$2
case_wasm=$3
host=$root/build/tools/leanexe-wasmtime-host
if [ ! -x "$host" ] || [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  echo "fail: $host is missing or older than tools/wasmtime-host.c; build it with tools/build-wasmtime-host.sh" >&2
  exit 1
fi
(cd "$root" && tools/leanrun --timeout 30m lake --log-level error build TestSupport.Native.ModuleCases)
cases=$(mktemp)
errors=$(mktemp)
trap 'rm -f "$cases" "$errors"' EXIT
# Native Lean panics on the reads past the end of an array that the cases exercise: it writes a
# message and a backtrace to standard error and returns Lean's default value.  The run fails when
# Lean exits with an error or writes any other message.
if ! (cd "$root" && tools/leanrun --timeout 10m lake env lean --run \
    tests/TestSupport/Native/ModuleCases.lean) >"$cases" 2>"$errors"; then
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
echo "native Lean: $reads reads past the end, as the cases expect"
declare -A passed
failed=0
while IFS='|' read -r module name result args expected; do
  if [ "$module" != "$case_module" ]; then
    continue
  fi
  read -ra argv <<<"$args"
  out=$("$host" call "$case_wasm" "$name" "$result" "${argv[@]}" | tr -d '[] ' | paste -sd, -)
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
[ "$total" -gt 0 ] && [ "$failed" -eq 0 ]
