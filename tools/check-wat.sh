#!/usr/bin/env bash
set -euo pipefail

# Verifies the two serializers of the one lowering: for each entry, the WAT
# text from compile-wat, parsed back to a binary by wasm-tools, must be
# byte-identical to the binary from compile.

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

wasm_tools="${WASM_TOOLS:-}"
if [[ -z "$wasm_tools" ]]; then
  if command -v wasm-tools >/dev/null 2>&1; then
    wasm_tools="$(command -v wasm-tools)"
  elif [[ -x "$HOME/.cargo/bin/wasm-tools" ]]; then
    wasm_tools="$HOME/.cargo/bin/wasm-tools"
  else
    echo "wasm-tools not found. Install it with cargo or set WASM_TOOLS." >&2
    exit 127
  fi
fi

lake build lean-wasm

out_dir="$repo_root/.lake/build/wat-check"
mkdir -p "$out_dir"

cases=(
  "LeanExe.Examples.TalosGcd LeanExe.Examples.TalosGcd.gcd"
  "LeanExe.Examples.TalosAssocList LeanExe.Examples.TalosAssocList.lookupDemo"
  "LeanExe.Examples.OrderBook LeanExe.Examples.OrderBook.matchBook"
  "LeanExe.Examples.AsciiDigits LeanExe.Examples.AsciiDigits.validateGeneric"
  "LeanExe.Examples.ByteArrayPrograms LeanExe.Examples.ByteArrayPrograms.appendBang"
  "LeanExe.Examples.ByteArrayPrograms LeanExe.Examples.ByteArrayPrograms.pushBangSize"
  "LeanExe.Examples.Collatz LeanExe.Examples.Collatz.steps"
  "LeanExe.Examples.Correctness LeanExe.Examples.Correctness.arrayFoldByteArrayAccumulatorReleaseStats"
  "LeanExe.Examples.JsonTypedDecode LeanExe.Examples.JsonTypedDecode.transform"
)

for case in "${cases[@]}"; do
  read -r module entry <<< "$case"
  name="${entry##*.}"
  lake build "$module" >/dev/null
  .lake/build/bin/lean-wasm compile --module "$module" --entry "$entry" \
    --out "$out_dir/$name.wasm"
  .lake/build/bin/lean-wasm compile-wat --module "$module" --entry "$entry" \
    --out "$out_dir/$name.wat"
  "$wasm_tools" parse "$out_dir/$name.wat" -o "$out_dir/$name.from-wat.wasm"
  if ! cmp -s "$out_dir/$name.wasm" "$out_dir/$name.from-wat.wasm"; then
    echo "WAT and binary serializers disagree for $entry" >&2
    exit 1
  fi
  echo "wat matches binary: $name"
done
