#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: check-talos-case.sh --case <name> --module <module> --entry <entry> --spec <target> --program <path> [--artifacts-only | --update]" >&2
  echo "  --program names the generated model file relative to proofs/talos/lean." >&2
  echo "  --artifacts-only compares WASM and WAT without building a proof." >&2
  echo "  --update replaces the checked-in proof inputs with fresh compiler output," >&2
  echo "  regenerates the Talos Program.lean model, and rebuilds the proof; on any" >&2
  echo "  failure it restores the previous proof inputs." >&2
  exit 2
}

case_name=""
module=""
entry=""
spec=""
program_path=""
artifacts_only=0
update=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --case) case_name="$2"; shift 2 ;;
    --module) module="$2"; shift 2 ;;
    --entry) entry="$2"; shift 2 ;;
    --spec) spec="$2"; shift 2 ;;
    --program) program_path="$2"; shift 2 ;;
    --artifacts-only) artifacts_only=1; shift ;;
    --update) update=1; shift ;;
    *) usage ;;
  esac
done
[[ -n "$case_name" && -n "$module" && -n "$entry" && -n "$spec" && -n "$program_path" ]] || usage
if [[ "$artifacts_only" -eq 1 && "$update" -eq 1 ]]; then
  echo "check-talos-case.sh: --artifacts-only and --update cannot be combined" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
wasm_tmp="$repo_root/.lake/build/talos-check/$case_name/program.wasm"
wat_tmp="$repo_root/.lake/build/talos-check/$case_name/program.wat"
wasm_ref="$repo_root/proofs/talos/rust/build/$case_name/program.wasm"
wat_ref="$repo_root/proofs/talos/rust/build/$case_name/program.wat"
verifier="$repo_root/proofs/talos/lean/.lake/packages/CodeLib/verifier/.lake/build/bin/verifier"
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
WASM_TOOLS="$wasm_tools" "$repo_root/tools/check-wasm-tools-version.sh"

cd "$repo_root"

if [[ "$artifacts_only" -eq 1 ]]; then
  lake --no-ansi --quiet --log-level=error build "$module"
  lake --no-ansi --quiet --log-level=error build lean-wasm
else
  lake --no-ansi build "$module"
  lake --no-ansi build lean-wasm
fi
mkdir -p "$(dirname "$wasm_tmp")"
.lake/build/bin/lean-wasm compile \
  --module "$module" \
  --entry "$entry" \
  --out "$wasm_tmp"
"$wasm_tools" print "$wasm_tmp" -o "$wat_tmp"

if [[ "$update" -eq 1 ]]; then
  if [[ ! -x "$verifier" ]]; then
    echo "Talos verifier not found at $verifier." >&2
    echo "Build it with: cd proofs/talos/lean/.lake/packages/CodeLib/verifier && lake build" >&2
    exit 127
  fi
  backup_dir="$(mktemp -d)"
  program_ref="$repo_root/proofs/talos/lean/$program_path"
  restore() {
    for file in "$wasm_ref" "$wat_ref" "$program_ref"; do
      local name
      name="$(basename "$file").$(basename "$(dirname "$file")")"
      if [[ -f "$backup_dir/$name" ]]; then
        cp "$backup_dir/$name" "$file"
      else
        rm -f "$file"
      fi
    done
    rm -rf "$backup_dir"
    echo "update failed; restored previous proof inputs for $case_name" >&2
  }
  trap restore ERR
  for file in "$wasm_ref" "$wat_ref" "$program_ref"; do
    if [[ -f "$file" ]]; then
      cp "$file" "$backup_dir/$(basename "$file").$(basename "$(dirname "$file")")"
    fi
  done
  mkdir -p "$(dirname "$wasm_ref")"
  cp "$wasm_tmp" "$wasm_ref"
  cp "$wat_tmp" "$wat_ref"
  (cd "$repo_root/proofs/talos" && "$verifier" emit --force-emit "$case_name")
  (cd "$repo_root/proofs/talos/lean" && lake --no-ansi build "$spec")
  trap - ERR
  rm -rf "$backup_dir"
  echo "Talos inputs updated and proof passed: $case_name"
else
  cmp "$wasm_tmp" "$wasm_ref"
  cmp "$wat_tmp" "$wat_ref"
  if [[ "$artifacts_only" -eq 1 ]]; then
    echo "Talos artifacts match: $case_name"
  else
    (cd "$repo_root/proofs/talos/lean" && lake --no-ansi build "$spec")
    echo "Talos case passed: $case_name"
  fi
fi
