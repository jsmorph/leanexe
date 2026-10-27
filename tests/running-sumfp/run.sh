#!/bin/sh
set -eu
set -f
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

group=full
talos_case=
case "$#:${1-}" in
  0:) ;;
  1:--native-wasm) group=native-wasm ;;
  1:--talos-only) group=talos ;;
  2:--talos-only) group=talos; talos_case=$2 ;;
  *) printf 'Usage: tests/running-sumfp/run.sh [--native-wasm | --talos-only [CASE_NAME]]\n' >&2; exit 2 ;;
esac

out="$root/build/running-sumfp"
host="$root/build/tools/leanexe-wasmtime-host"
case "$group" in
  full)
    tools/leanrun --timeout 30m --log build/running-sumfp/build.log lake build \
      Demos.RunningSumFp.Correct Verified.Wasi.ScriptHostContracts running-sumfp-native ;;
  native-wasm)
    tools/leanrun --timeout 30m --log build/running-sumfp/build.log lake build \
      Demos.RunningSumFp.Correct running-sumfp-native ;;
  talos)
    tools/leanrun --timeout 30m --log build/running-sumfp/build.log lake build \
      Demos.RunningSumFp.Correct Verified.Wasi.ScriptHostContracts ;;
esac
tools/leanrun --timeout 5m lake env lean tests/running-sumfp/StreamAxioms.lean
tools/leanrun --timeout 5m lake env lean tests/running-sumfp/Axioms.lean

if [ "$group" != talos ]; then
tools/leanrun --timeout 5m lake env lean --run tests/running-sumfp/Numbers.lean
tools/leanrun --timeout 5m lake env lean --run tests/running-sumfp/Stream.lean
tools/leanrun --timeout 5m lake env lean --run tests/running-sumfp/Cases.lean "$out/cases"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Demos.RunningSumFp.Module \
  Demos.RunningSumFp.module "$out/sumfp.wasm"
wasm-tools validate "$out/sumfp.wasm"

if [ ! -x "$host" ]; then
  printf 'Missing Wasmtime host: %s\n' "$host" >&2
  exit 1
fi
if [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  printf 'Native host is older than tools/wasmtime-host.c; rebuild it with tools/build-wasmtime-host.sh\n' >&2
  exit 1
fi

count=0
tab=$(printf '\t')
while IFS="$tab" read -r name expected_status; do
  case $expected_status in
    ''|*[!0-9]*)
      printf '%s: expected status is not a decimal number: %s\n' "$name" "$expected_status" >&2
      exit 1 ;;
  esac
  directory="$out/cases/$name"
  mkdir -p "$directory"
  status=0
  timeout 60s .lake/build/bin/running-sumfp-native <"$out/cases/$name.input" \
    >"$directory/native.stdout" 2>"$directory/native.stderr" || status=$?
  if [ "$status" -ne "$expected_status" ]; then
    printf '%s: native status %s, expected %s\n' "$name" "$status" "$expected_status" >&2
    exit 1
  fi
  cmp "$out/cases/$name.expected" "$directory/native.stdout"
  test ! -s "$directory/native.stderr"
  status=0
  timeout 60s "$host" --stdin-file "$out/cases/$name.input" \
    --stdout-file "$directory/wasm.stdout" --stderr-file "$directory/wasm.stderr" \
    --control-file "$directory/control" run "$out/sumfp.wasm" \
    >"$directory/host.stdout" 2>"$directory/host.stderr" || status=$?
  if [ "$status" -ne "$expected_status" ]; then
    printf '%s: Wasm status %s, expected %s\n' "$name" "$status" "$expected_status" >&2
    cat "$directory/host.stderr" >&2
    exit 1
  fi
  cmp "$out/cases/$name.expected" "$directory/wasm.stdout"
  test ! -s "$directory/wasm.stderr"
  test ! -s "$directory/host.stdout"
  test ! -s "$directory/host.stderr"
  printf 'wasi-exit %s\n' "$expected_status" >"$directory/expected.control"
  cmp "$directory/expected.control" "$directory/control"
  count=$((count + 1))
done <"$out/cases/cases.tsv"
printf 'Running sumfp native/Wasm comparisons: %s cases passed\n' "$count"

uv run tests/running-sumfp/interactive.py
tests/wasi/stream-io-errors.sh running-sumfp .lake/build/bin/running-sumfp-native "$out/sumfp.wasm"
fi

if [ "$group" != native-wasm ]; then
  if [ -n "$talos_case" ]; then
    tools/leanrun --timeout 5m lake env lean --run tests/running-sumfp/Talos.lean "$talos_case"
  else
    tools/leanrun --timeout 5m lake env lean --run tests/running-sumfp/Talos.lean
  fi
fi
