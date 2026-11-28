#!/usr/bin/env bash
# Checks Library.Regex.matchWith in native Lean against Library.Regex.Spec.answer and against
# Python's re.fullmatch, with the compiled executables regex-native and regex-python-cases.
# Usage: tests/regex/run.sh
set -euo pipefail
if [ "$#" -ne 0 ]; then
  echo "usage: tests/regex/run.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
cases=$(mktemp)
trap 'rm -f "$cases"' EXIT
tools/leanrun --timeout 30m lake build regex-native regex-python-cases
tools/leanrun --timeout 90m .lake/build/bin/regex-native
tools/leanrun --timeout 60m .lake/build/bin/regex-python-cases >"$cases"
uv run tests/regex/python_check.py <"$cases"
