#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case shared_pair \
  --module LeanExe.Examples.ByteArrayPrograms \
  --entry LeanExe.Examples.ByteArrayPrograms.sharedPushPair \
  --spec Project.SharedPair.Spec \
  --program Project/SharedPair/Program.lean \
  "$@"
