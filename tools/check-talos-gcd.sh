#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case gcd \
  --module LeanExe.Examples.TalosGcd \
  --entry LeanExe.Examples.TalosGcd.gcd \
  --spec Project.Gcd.Spec \
  "$@"
