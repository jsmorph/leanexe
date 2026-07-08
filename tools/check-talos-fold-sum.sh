#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case fold_sum \
  --module LeanExe.Examples.ByteArrayPrograms \
  --entry LeanExe.Examples.ByteArrayPrograms.foldSum \
  --spec Project.FoldSum.Spec \
  --program Project/FoldSum/Program.lean \
  "$@"
