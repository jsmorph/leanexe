#!/usr/bin/env bash
set -euo pipefail

exec "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/check-talos-case.sh" \
  --case assoc_list \
  --module LeanExe.Examples.TalosAssocList \
  --entry LeanExe.Examples.TalosAssocList.lookupDemo \
  --spec Project.AssocList.Spec \
  --program Project/AssocList/Program.lean \
  "$@"
