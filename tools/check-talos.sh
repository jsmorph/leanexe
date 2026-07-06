#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

tools/check-talos-gcd.sh "$@"
tools/check-talos-assoc-list.sh "$@"
tools/check-talos-order-book.sh "$@"
tools/check-talos-validate.sh "$@"

cd "$repo_root/proofs/talos-gcd/lean"
lake build Project
