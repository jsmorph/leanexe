#!/usr/bin/env bash
# The integration test of the passive-safety check.  It builds the case executable, prints the
# inputs and results of Demos.PassiveSafety.check for the cases of
# tests/TestSupport/PassiveSafety/Cases.lean, and checks them with
# tests/passivesafety/reference.py against numerical integration of the Hill-Clohessy-Wiltshire
# equations.  It writes the report to build/passivesafety/reference.txt.
# Usage: tests/passivesafety/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/passivesafety
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-passivesafety
.lake/build/bin/verified-cases-passivesafety --bits >"$out/cases.txt"
uv run tests/passivesafety/reference.py "$out/cases.txt" | tee "$out/reference.txt"
