#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root/proofs/talos/lean"

lake --no-ansi build Project
echo "Talos proof setup complete: Project is up to date"
