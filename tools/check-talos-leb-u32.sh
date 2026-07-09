#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case leb_u32 \
  --module LeanExe.Wasm.Leb \
  --entry LeanExe.Wasm.Leb.u32lebU64 \
  --spec Project.LebU32.Spec \
  --program Project/LebU32/Program.lean \
  "$@"
