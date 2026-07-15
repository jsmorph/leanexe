#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

usage() {
  echo "usage: check-talos.sh [--artifacts-only | --update]" >&2
  echo "  --artifacts-only compares all checked WASM and WAT without checking proofs." >&2
  echo "  --update transactionally updates and proves every artifact." >&2
  exit 2
}

mode="check"
if [[ $# -gt 1 ]]; then
  usage
elif [[ $# -eq 1 ]]; then
  case "$1" in
    --artifacts-only) mode="artifacts" ;;
    --update) mode="update" ;;
    *) usage ;;
  esac
fi

case_scripts=(
  tools/check-talos-gcd.sh
  tools/check-talos-assoc-list.sh
  tools/check-talos-order-book.sh
  tools/check-talos-validate.sh
  tools/check-talos-append-bang.sh
  tools/check-talos-push-size.sh
  tools/check-talos-push-twice.sh
  tools/check-talos-shared-pair.sh
  tools/check-talos-pair-free.sh
  tools/check-talos-box-free.sh
  tools/check-talos-fold-sum.sh
  tools/check-talos-leb-u32.sh
  tools/check-talos-clob-quote.sh
  tools/check-talos-clob-cancel.sh
  tools/check-talos-clob-find-best.sh
  tools/check-talos-clob-post-only.sh
  tools/check-talos-clob-match-fuel.sh
)

if [[ "$mode" == "update" ]]; then
  for script in "${case_scripts[@]}"; do
    "$script" --update
  done

  cd "$repo_root/proofs/talos-gcd/lean"
  lake --no-ansi build Project
  echo "Talos update passed: 17 artifacts and the complete proof library"
  exit 0
fi

for script in "${case_scripts[@]}"; do
  "$script" --artifacts-only
done

if [[ "$mode" == "artifacts" ]]; then
  echo "Talos artifact gate passed: 17 WASM and WAT pairs match"
  exit 0
fi

cd "$repo_root/proofs/talos-gcd/lean"
if ! lake --no-ansi --quiet --log-level=error --no-build build Project; then
  echo "Talos proof outputs are missing or out of date." >&2
  echo "Build them first with tools/setup-talos.sh from the repository root." >&2
  exit 1
fi
echo "Talos gate passed: 17 artifacts match and the proof library is up to date"
