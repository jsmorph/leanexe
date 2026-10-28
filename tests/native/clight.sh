#!/usr/bin/env bash
# Compares LClight.run with CompCert's reference interpreter on random programs.  The executable
# clight-diff (tests/TestSupport/Native/ClightDiff.lean) writes COUNT programs from SEED as C,
# and the fixed programs of ClightGen.nanPrograms, each with the output that LClight.run gives
# under the NaN parameters of ARCHI; then `ccomp -interp -quiet` runs each C file.  A program that LClight.run finds stuck must stop with
# CompCert's "Undefined behavior", and every other program must print the same lines.  A program
# whose run exhausts the fuel is counted and skipped.  CCOMP names the CompCert 3.18 driver,
# `ccomp` by default, configured for the target of ARCHI.
# LEANRUN_MEMORY_HIGH is the memory limit of each step that runs under tools/leanrun, 6G unless
# the caller sets it, as for tests/native/run.sh.
# Usage: tests/native/clight.sh SEED COUNT [x86_64|aarch64]
set -euo pipefail
export LEANRUN_MEMORY_HIGH=${LEANRUN_MEMORY_HIGH:-6G}
if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
  echo "usage: tests/native/clight.sh SEED COUNT [x86_64|aarch64]" >&2
  exit 2
fi
seed=$1
count=$2
archi=${3:-x86_64}
ccomp=${CCOMP:-ccomp}
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$root/build/native/clight/$seed
cd "$root"
tools/leanrun --timeout 60m lake build clight-diff
rm -rf "$out"
tools/leanrun --timeout 60m .lake/build/bin/clight-diff "$seed" "$count" "$archi" "$out"
pass=0
undefined=0
fuel=0
fail=0
for c in "$out"/*.c; do
  t=${c%.c}
  expected=$(cat "$t.expected")
  if [ "$expected" = "FUEL" ]; then
    fuel=$((fuel + 1))
    continue
  fi
  set +e
  actual=$("$ccomp" -interp -quiet "$c" 2>"$t.err")
  status=$?
  set -e
  if [ "$status" -eq 126 ] && grep -q "Undefined behavior" <<<"$actual"; then
    actual=UB
  elif [ "$status" -ne 0 ]; then
    echo "fail: ${t##*/}: ccomp exited with status $status" >&2
    fail=$((fail + 1))
    continue
  fi
  if [ "$actual" = "$expected" ]; then
    pass=$((pass + 1))
    if [ "$actual" = UB ]; then
      undefined=$((undefined + 1))
    fi
  else
    echo "fail: ${t##*/}" >&2
    diff <(echo "$expected") <(echo "$actual") >&2 || true
    fail=$((fail + 1))
  fi
done
echo "clight: $pass agree ($undefined undefined), $fail differ, $fuel out of fuel"
[ "$fail" -eq 0 ]
