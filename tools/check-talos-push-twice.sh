#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case push_twice \
  --module LeanExe.Examples.ByteArrayPrograms \
  --entry LeanExe.Examples.ByteArrayPrograms.pushTwiceSizes \
  --spec Project.PushTwice.Spec \
  --program Project/PushTwice/Program.lean \
  "$@"
