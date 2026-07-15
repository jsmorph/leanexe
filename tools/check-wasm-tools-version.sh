#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
expected="$(<"$repo_root/.wasm-tools-version")"
wasm_tools="${WASM_TOOLS:-}"

if [[ -z "$wasm_tools" ]]; then
  if command -v wasm-tools >/dev/null 2>&1; then
    wasm_tools="$(command -v wasm-tools)"
  elif [[ -x "$HOME/.cargo/bin/wasm-tools" ]]; then
    wasm_tools="$HOME/.cargo/bin/wasm-tools"
  else
    echo "wasm-tools not found. Install version $expected or set WASM_TOOLS." >&2
    exit 127
  fi
fi

if [[ ! -x "$wasm_tools" ]]; then
  echo "wasm-tools is not executable: $wasm_tools" >&2
  exit 127
fi

if ! actual="$($wasm_tools --version 2>&1)"; then
  echo "wasm-tools version command failed: $wasm_tools --version" >&2
  exit 1
fi

if [[ "$actual" != "wasm-tools $expected" ]]; then
  actual_first_line="${actual%%$'\n'*}"
  echo "wasm-tools version mismatch: expected $expected, got $actual_first_line" >&2
  echo "Executable: $wasm_tools" >&2
  exit 1
fi

echo "checked wasm-tools $expected"
