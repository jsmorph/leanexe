#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case append_bang \
  --module LeanExe.Examples.ByteArrayPrograms \
  --entry LeanExe.Examples.ByteArrayPrograms.appendBang \
  --spec Project.AppendBang.Spec \
  --program Project/AppendBang/Program.lean \
  "$@"
