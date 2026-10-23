#!/bin/sh
set -eu
set -f
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

tools/leanrun --timeout 10m --log build/wasi/foundations.log lake build \
  Verified.Bytes.CopyOwned Verified.Bytes.Release Verified.Bytes.Get \
  Verified.Bytes.LiteralFrame LeanExe.Wasi.Prefix
tools/leanrun --timeout 30m --log build/wasi/byte-values.log lake build Verified.Examples.Bytes
tools/leanrun --timeout 5m lake env lean tests/wasi/Bytes.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/Code.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/Axioms.lean

out="$root/build/wasi"
host="$root/build/tools/leanexe-wasmtime-host"
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.Bytes \
  Verified.Examples.Bytes.compiled.module "$out/bytes.wasm"
wasm-tools validate "$out/bytes.wasm"

tab=$(printf '\t')
count=0
while IFS="$tab" read -r export_name kind arguments expected allocations releases; do
  if [ "$expected" = _ ]; then expected=; fi
  set -- $arguments
  observed=$("$host" call-stats "$out/bytes.wasm" "$export_name" "$kind" "$@")
  wanted=$(printf '%s\nstats %s %s' "$expected" "$allocations" "$releases")
  if [ "$observed" != "$wanted" ]; then
    printf '%s\n' "failed: $export_name $arguments" "expected: $wanted" "observed: $observed" >&2
    exit 1
  fi
  count=$((count + 1))
done <"$root/tests/wasi/bytes.tsv"
printf 'Byte execution tests passed: %s cases\n' "$count"
