#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case clob_limit \
  --module LeanExe.Examples.Clob \
  --entry LeanExe.Examples.Clob.limit \
  --spec Project.ClobLimit.Spec \
  --program Project/ClobLimit/Program.lean \
  "$@"
