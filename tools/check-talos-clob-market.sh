#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case clob_market \
  --module LeanExe.Examples.Clob \
  --entry LeanExe.Examples.Clob.market \
  --spec Project.ClobMarket.Spec \
  --program Project/ClobMarket/Program.lean \
  "$@"
