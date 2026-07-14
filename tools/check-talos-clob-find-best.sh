#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case clob_find_best \
  --module LeanExe.Examples.Clob \
  --entry LeanExe.Examples.Clob.findBest \
  --spec Project.ClobFindBest.Spec \
  --program Project/ClobFindBest/Program.lean \
  "$@"
