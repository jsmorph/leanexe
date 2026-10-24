#!/usr/bin/env bash
# Checks Library.Regex.matchWith in native Lean against Library.Regex.Spec.answer and against
# Python's re.fullmatch.  Usage: tests/regex/run.sh
set -euo pipefail
if [ "$#" -ne 0 ]; then
  echo "usage: tests/regex/run.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
cases=$(mktemp)
trap 'rm -f "$cases"' EXIT
tools/leanrun --timeout 30m lake build Library.Regex.Program Library.Regex.Spec \
  Library.Bytes.Packed TestSupport.Regex.Generate
tools/leanrun --timeout 90m lake env lean --run tests/TestSupport/Regex/Native.lean
tools/leanrun --timeout 60m lake env lean --run tests/TestSupport/Regex/PythonCases.lean >"$cases"
python3 -I tests/regex/python_check.py <"$cases"
