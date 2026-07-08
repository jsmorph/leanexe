#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case box_free \
  --module LeanExe.Examples.ByteArrayPrograms \
  --entry LeanExe.Examples.ByteArrayPrograms.boxFreeStats \
  --spec Project.BoxFree.Spec \
  --program Project/BoxFree/Program.lean \
  "$@"
