#!/usr/bin/env bash
# Elaborates the modules of tests/TestSupport/A64/Isla, which prove Agrees
# (LeanExe/A64/Isla/Check.lean) for the forms of LeanExe/A64/Machine.lean from the traces of
# tests/isla, and prints the axioms of each theorem that a module names in #print axioms.  Lake
# does not track the files that isla_trace% and isla_features% read, so an olean can hold theorems
# about files that have since changed.  The script therefore builds only the modules' imports with
# Lake and elaborates each module with lean, which reads the files as they stand, and Profiles.lean
# checks the profiles' olean against the features files.  No module of the directory may import
# another, and no default build target includes them.  The script fails if an elaboration fails,
# if a module prints no axioms, or if a theorem depends on an axiom other than propext,
# Classical.choice, and Quot.sound.
# Usage: tests/isla/theorems.sh [MODULE...]
# MODULE is the name of a file of tests/TestSupport/A64/Isla without .lean, such as Register; the
# script elaborates every module there unless given some.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
if [ "$#" -eq 0 ]; then
  set -- $(basename -s .lean tests/TestSupport/A64/Isla/*.lean)
fi
files=()
for m in "$@"; do
  files+=("tests/TestSupport/A64/Isla/$m.lean")
done
imports=$(sed -n 's/^import //p' "${files[@]}" | sort -u)
if grep -q '^TestSupport\.A64\.Isla\.' <<<"$imports"; then
  echo "fail: a module imports another module of tests/TestSupport/A64/Isla"
  exit 1
fi
tools/leanrun --timeout 60m --memory-high 8G --cpus 4 lake --log-level error build $imports
std='(propext|Classical\.choice|Quot\.sound)'
status=0
for f in "${files[@]}"; do
  start=$(date +%s)
  if ! out=$(tools/leanrun --timeout 180m --memory-high 8G --cpus 4 lake env lean "$f" 2>&1); then
    printf '%s\n' "$out"
    echo "fail: $f"
    status=1
    continue
  fi
  echo "$f: $(($(date +%s) - start)) s"
  axioms=$(grep -E "depends on axioms|does not depend on any axioms" <<<"$out" || true)
  if [ -z "$axioms" ]; then
    echo "fail: $f prints no axioms"
    status=1
    continue
  fi
  printf '%s\n' "$axioms"
  bad=$(grep "depends on axioms" <<<"$axioms" |
    grep -vE "depends on axioms: \[$std(, $std)*\]$" || true)
  if [ -n "$bad" ]; then
    echo "fail: $f: an axiom other than propext, Classical.choice, and Quot.sound"
    status=1
  fi
done
exit "$status"
