#!/bin/sh
set -eu
set -f
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

out="$root/build/running-sum"
host="$root/build/tools/leanexe-wasmtime-host"
tools/leanrun --timeout 15m --log build/running-sum/build.log lake build \
  Demos.RunningSum.Correct \
  Verified.Examples.WasiProcess Verified.Wasi.ProcessTermination running-sum-native
tools/leanrun --timeout 5m lake env lean tests/running-sum/Axioms.lean
tools/leanrun --timeout 5m lake env lean tests/running-sum/MathAxioms.lean
tools/leanrun --timeout 5m lake env lean tests/running-sum/CorrectAxioms.lean
tools/leanrun --timeout 5m lake env lean tests/running-sum/ProcessAxioms.lean
tools/leanrun --timeout 5m lake env lean --run tests/running-sum/Arithmetic.lean
tools/leanrun --timeout 5m lake env lean --run tests/running-sum/Stream.lean
tools/leanrun --timeout 5m lake env lean --run tests/running-sum/Talos.lean
tools/leanrun --timeout 5m lake env lean --run tests/running-sum/Cases.lean "$out/cases"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Demos.RunningSum.Module \
  Demos.RunningSum.module "$out/sum.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiProcess \
  Verified.Examples.WasiProcess.module "$out/process.wasm"
wasm-tools validate "$out/sum.wasm"
wasm-tools validate "$out/process.wasm"

if [ ! -x "$host" ]; then
  printf 'Missing Wasmtime host: %s\n' "$host" >&2
  exit 1
fi

count=0
tab=$(printf '\t')
while IFS="$tab" read -r name expected_status; do
  directory="$out/cases/$name"
  mkdir -p "$directory"
  status=0
  timeout 60s .lake/build/bin/running-sum-native <"$out/cases/$name.input" \
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
    --control-file "$directory/control" run "$out/sum.wasm" \
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
printf 'Running sum native/Wasm comparisons: %s cases passed\n' "$count"

timeout 30s "$host" --stdin-file tests/wasi/host/empty.bin \
  --stdout-file "$out/process.stdout" --stderr-file "$out/process.stderr" \
  --control-file "$out/process.control" run "$out/process.wasm"
printf 'ABC' >"$out/process.expected"
cmp "$out/process.expected" "$out/process.stdout"
cmp tests/wasi/host/exit-0.control "$out/process.control"
test ! -s "$out/process.stderr"
uv run tests/running-sum/interactive.py
tests/wasi/stream-io-errors.sh running-sum .lake/build/bin/running-sum-native "$out/sum.wasm"
