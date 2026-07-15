#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case clob_match_fuel \
  --module LeanExe.Examples.Clob \
  --entry LeanExe.Examples.Clob.matchFuel \
  --spec Project.ClobMatchFuel.Spec \
  --program Project/ClobMatchFuel/Program.lean \
  "$@"
