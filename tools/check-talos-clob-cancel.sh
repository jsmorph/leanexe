#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case clob_cancel \
  --module LeanExe.Examples.Clob \
  --entry LeanExe.Examples.Clob.cancel \
  --spec Project.ClobCancel.Spec \
  --program Project/ClobCancel/Program.lean \
  "$@"
