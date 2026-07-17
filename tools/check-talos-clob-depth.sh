#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case clob_depth \
  --module LeanExe.Examples.Clob \
  --entry LeanExe.Examples.Clob.depth \
  --spec Project.ClobDepth.Spec \
  --program Project/ClobDepth/Program.lean \
  "$@"
