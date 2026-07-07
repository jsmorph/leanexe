#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case pair_free \
  --module LeanExe.Examples.ByteArrayPrograms \
  --entry LeanExe.Examples.ByteArrayPrograms.sharedPairFreeStats \
  --spec Project.PairFree.Spec \
  --program Project/PairFree/Program.lean \
  "$@"
