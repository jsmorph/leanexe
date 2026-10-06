#!/usr/bin/env bash
# Writes tests/drone/corpus.txt, the terrains of tests/drone/OracleDriver.lean and the earlier
# system's `compute` of each, and tests/drone/cases.txt, calls of the earlier system's other
# functions and their results, run natively from the earlier system's Examples/Drone/Program.lean at
# commit 188ccb4d.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$root/tmp"
source=$(mktemp "$root/tmp/drone-oracle-XXXXXX.lean")
trap 'rm -f "$source"' EXIT
git -C "$root" show 188ccb4dd7498d9f7189a3a7f1c199f20f4644c8:Examples/Drone/Program.lean >"$source"
cat "$root/tests/drone/OracleDriver.lean" >>"$source"
cd "$root"
tools/leanrun --timeout 1h --lock-timeout 1200 lake env lean --run "$source" corpus >tests/drone/corpus.txt
tools/leanrun --timeout 1h --lock-timeout 1200 lake env lean --run "$source" cases >tests/drone/cases.txt
