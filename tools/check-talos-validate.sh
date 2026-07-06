#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case validate \
  --module LeanExe.Examples.AsciiDigits \
  --entry LeanExe.Examples.AsciiDigits.validateGeneric \
  --spec Project.Validate.Spec \
  --program Project/Validate/Program.lean \
  "$@"
