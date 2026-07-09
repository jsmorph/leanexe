#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case clob_quote \
  --module LeanExe.Examples.Clob \
  --entry LeanExe.Examples.Clob.quote \
  --spec Project.ClobQuote.Spec \
  --program Project/ClobQuote/Program.lean \
  "$@"
