#!/usr/bin/env bash
# Compares LClight.run with CompCert's reference interpreter on random programs.  The executable
# clight-diff (tests/TestSupport/Native/ClightDiff.lean) writes COUNT programs from SEED as C,
# and the fixed programs of ClightGen.nanPrograms, each with the output that LClight.run gives
# under the NaN parameters of ARCHI, and `ccomp -interp -quiet` runs each C file.  It also writes
# COUNT trace programs, whose main stores to volatile globals, with the events and the exit code
# that LClight.run_program gives, and `ccomp -interp` runs each of them, and COUNT input
# programs, which also load from const volatile globals, in the same way.  A program that the
# copy finds stuck must stop with CompCert's "Undefined behavior", and every other program must
# print the same lines, the events and the exit code for a trace program.  A program whose run
# exhausts the fuel is counted and skipped.  CCOMP names the CompCert 3.18 driver, `ccomp` by
# default, configured for the target of ARCHI.
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
traces=0
inputs=0
for c in "$out"/t*.c "$out"/nan*.c; do
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
# Trace programs: ccomp -interp prints each observable event and the exit code, each line after
# the prefix "Time N: ", and may break a long line before an indented continuation.
for c in "$out"/v*.c "$out"/w*.c; do
  t=${c%.c}
  expected=$(cat "$t.expected")
  if [ "$expected" = "FUEL" ]; then
    fuel=$((fuel + 1))
    continue
  fi
  set +e
  raw=$("$ccomp" -interp "$c" 2>"$t.err")
  set -e
  if grep -q "Undefined behavior" <<<"$raw"; then
    actual=UB
  else
    actual=$(awk '/^ / { sub(/^ +/, " "); line = line $0; next }
      { if (seen) print line; line = $0; seen = 1 }
      END { if (seen) print line }' <<<"$raw" | sed 's/^Time [0-9]*: //')
  fi
  if [ "$actual" = "$expected" ]; then
    pass=$((pass + 1))
    case ${t##*/} in
      v*) traces=$((traces + 1)) ;;
      *) inputs=$((inputs + 1)) ;;
    esac
    if [ "$actual" = UB ]; then
      undefined=$((undefined + 1))
    fi
  else
    echo "fail: ${t##*/}" >&2
    diff <(echo "$expected") <(echo "$actual") >&2 || true
    fail=$((fail + 1))
  fi
done
echo "clight: $pass agree ($undefined undefined, $traces trace programs, $inputs input programs), $fail differ, $fuel out of fuel"
[ "$fail" -eq 0 ]
