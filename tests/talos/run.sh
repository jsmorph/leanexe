#!/usr/bin/env bash
# Tests Talos, the WebAssembly semantics of the theorems, with the WebAssembly testsuite at the
# CodeLib revision that lake-manifest.json pins.  The suite is CodeLib's submodule
# vendor/testsuite, which must be initialized at the revision CodeLib records.  The script builds
# Talos's runner, interpreter/Interpreter/Testsuite.lean, runs it over the suite, and fails unless
# it exits with status 0, which it does when no command fails, raises an interpreter error, or
# exhausts its fuel.  It then compares the runner's --report output with testsuite_report.txt at
# CodeLib's root, which Talos's continuous integration compares in the same way.  The runner reads
# the suite at the relative path vendor/testsuite, so it runs from the CodeLib checkout.  Its
# temporary directory, its output run.txt, and its report report.txt lie in build/talos.  The
# runner splits each script with wasm-tools json-from-wast, and CodeLib's report holds only for the
# pinned version, so the script puts the directory of WASM_TOOLS, when it is set, first on PATH and
# checks the version of the wasm-tools that PATH gives.
# Usage: tests/talos/run.sh
set -euo pipefail
PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"
if [ -n "${WASM_TOOLS:-}" ]; then
  PATH="$(dirname "$WASM_TOOLS"):$PATH"
fi
export PATH
root=$(cd "$(dirname "$0")/../.." && pwd)
codelib=$root/.lake/packages/CodeLib
runner=$codelib/interpreter/.lake/build/bin/testsuite
out=$root/build/talos
cd "$root"
suite=$(git -C "$codelib" submodule status vendor/testsuite)
if [ "${suite:0:1}" != " " ]; then
  echo "talos: vendor/testsuite is not at the revision CodeLib records: $suite" >&2
  echo "talos: run git -C .lake/packages/CodeLib submodule update --init vendor/testsuite" >&2
  exit 2
fi
env -u WASM_TOOLS tools/check-wasm-tools-version.sh
tools/leanrun --timeout 3h lake build testsuite
mkdir -p "$out"
cd "$codelib"
# TMPDIR is set inside the scope because tools/leanrun derives its default lock directory from it.
status=0
"$root/tools/leanrun" --timeout 30m env TMPDIR="$out" "$runner" >"$out/run.txt" || status=$?
sed -n 's/^Totals: //p' "$out/run.txt" | awk '{ for (i = 1; i < NF; i += 2) print "talos: " $(i + 1) " " $i }'
if [ "$status" -ne 0 ]; then
  echo "talos: the runner exited with status $status, and build/talos/run.txt holds its output" >&2
  exit "$status"
fi
"$root/tools/leanrun" --timeout 30m env TMPDIR="$out" "$runner" --report >"$out/report.txt"
if ! diff -u testsuite_report.txt "$out/report.txt"; then
  echo "talos: the report differs from CodeLib's testsuite_report.txt" >&2
  exit 1
fi
echo "talos: the report of $(wc -l <"$out/report.txt") commands equals CodeLib's testsuite_report.txt"
