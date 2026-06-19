#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
wasm_tmp="$repo_root/.lake/build/talos-assoc-list/check.program.wasm"
wat_tmp="$repo_root/.lake/build/talos-assoc-list/check.program.wat"
wasm_ref="$repo_root/proofs/talos-gcd/rust/build/assoc_list/program.wasm"
wat_ref="$repo_root/proofs/talos-gcd/rust/build/assoc_list/program.wat"
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

cd "$repo_root"

lake build LeanExe.Examples.TalosAssocList lean-wasm
mkdir -p "$(dirname "$wasm_tmp")"
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.TalosAssocList \
  --entry LeanExe.Examples.TalosAssocList.lookupDemo \
  --out "$wasm_tmp"
"$wasm_tools" print "$wasm_tmp" > "$wat_tmp"

cmp "$wasm_tmp" "$wasm_ref"
cmp "$wat_tmp" "$wat_ref"

cd "$repo_root/proofs/talos-gcd/lean"
lake build Project.AssocList.Spec
