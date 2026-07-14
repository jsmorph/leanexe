#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case clob_post_only \
  --module LeanExe.Examples.Clob \
  --entry LeanExe.Examples.Clob.postOnly \
  --spec Project.ClobPostOnly.Spec \
  --program Project/ClobPostOnly/Program.lean \
  "$@"
