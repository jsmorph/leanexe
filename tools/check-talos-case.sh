#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: check-talos-case.sh --case <name> --module <module> --entry <entry> --spec <target> [--update]" >&2
  echo "  --update replaces the checked-in proof inputs with fresh compiler output" >&2
  echo "  and regenerates the Talos Program.lean model before rebuilding the proof." >&2
  exit 2
}

case_name=""
module=""
entry=""
spec=""
update=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --case) case_name="$2"; shift 2 ;;
    --module) module="$2"; shift 2 ;;
    --entry) entry="$2"; shift 2 ;;
    --spec) spec="$2"; shift 2 ;;
    --update) update=1; shift ;;
    *) usage ;;
  esac
done
[[ -n "$case_name" && -n "$module" && -n "$entry" && -n "$spec" ]] || usage

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
wasm_tmp="$repo_root/.lake/build/talos-check/$case_name/program.wasm"
wat_tmp="$repo_root/.lake/build/talos-check/$case_name/program.wat"
wasm_ref="$repo_root/proofs/talos-gcd/rust/build/$case_name/program.wasm"
wat_ref="$repo_root/proofs/talos-gcd/rust/build/$case_name/program.wat"
verifier="$repo_root/proofs/talos-gcd/lean/.lake/packages/CodeLib/verifier/.lake/build/bin/verifier"
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

lake build "$module" lean-wasm
mkdir -p "$(dirname "$wasm_tmp")"
.lake/build/bin/lean-wasm compile \
  --module "$module" \
  --entry "$entry" \
  --out "$wasm_tmp"
"$wasm_tools" print "$wasm_tmp" -o "$wat_tmp"

if [[ "$update" -eq 1 ]]; then
  if [[ ! -x "$verifier" ]]; then
    echo "Talos verifier not found at $verifier." >&2
    echo "Build it with: cd proofs/talos-gcd/lean/.lake/packages/CodeLib/verifier && lake build" >&2
    exit 127
  fi
  cp "$wasm_tmp" "$wasm_ref"
  cp "$wat_tmp" "$wat_ref"
  (cd "$repo_root/proofs/talos-gcd" && "$verifier" emit --force-emit "$case_name")
else
  cmp "$wasm_tmp" "$wasm_ref"
  cmp "$wat_tmp" "$wat_ref"
fi

cd "$repo_root/proofs/talos-gcd/lean"
lake build "$spec"
