#!/usr/bin/env bash
# The Linux executables of the AArch64 back end on an AArch64 Linux host: the flip of bit 5 of
# each byte of tests/TestSupport/A64/FlipElf.lean, which reads standard input to its end and
# writes the flipped bytes to standard output.  a64-elf emit writes flip.elf and, for each case,
# the message and the bytes that standard output must receive.  Lean then elaborates
# tests/TestSupport/A64/ImageFilesFlipElf.lean in the directory of those files, so that the kernel
# checks that flip.elf holds the bytes that its generator gives and proves its theorems, each with
# no axiom beyond propext, Classical.choice, and Quot.sound.  The script runs the executable on the
# host's processor and under qemu-aarch64, QEMU's user-mode emulator, each run within TIMEOUT
# seconds, 120 unless set, in a scope of one core and 2G of memory.  Each case runs from a file and
# from a pipe into which the script writes the message in pieces of 1, 3, 5, and 7 bytes, each
# after a pause of PAUSE seconds, 0.2 unless set, and then the rest.  A message of at most
# 8,800,000 bytes must give the flipped message and status 0, and a longer one status 64 and no
# output.  On the host's processor, runs outside the theorems exercise the error paths: standard
# input closed or a directory gives status 65 and no output, standard output closed or /dev/full
# status 66, and a file size limit with SIGXFSZ ignored a short write and then EFBIG, so status
# 66 after a prefix of the output.  A reader that closes standard output early ends the process
# with SIGPIPE, status 141, which the theorems leave out.  The products lie in OUT,
# build/linux/a64-elf unless set.
# Usage: tests/linux/a64-elf.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/linux/a64-elf}")
qemu=${QEMU_USER:-/usr/bin/qemu-aarch64}
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build a64-elf \
  TestSupport.A64.FlipElf LeanExe.A64.File
status=0
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-elf emit "$out" || status=1
chmod +x "$out/flip.elf"
# Elaborates the module $1 of tests/TestSupport/A64 in the directory of the files and requires $2
# lines of axioms, each a subset of the standard three.
kernel_check() {
  if tools/leanrun --timeout 60m --memory-high 8G lake env sh -c 'cd "$1" && lean "$2"' sh "$out" \
      "$root/tests/TestSupport/A64/$1.lean" >"$out/$1.check" 2>&1 &&
      [ "$(grep -c "depends on axioms\|does not depend on any axioms" "$out/$1.check")" = "$2" ] &&
      ! grep "depends on axioms" "$out/$1.check" |
        sed 's/.*depends on axioms: \[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
        grep -qvx 'propext\|Classical.choice\|Quot.sound'; then
    echo "pass: the kernel's check of $1.lean"
  else
    echo "fail: the kernel's check of $1.lean: $(head -c 600 "$out/$1.check")"
    status=1
  fi
}
kernel_check ImageFilesFlipElf 5
# Runs the command given as arguments in a scope of one core and 2G of memory.
scoped() {
  systemd-run --user --scope -q -p CPUQuota=100% -p MemoryMax=2G timeout "${TIMEOUT:-120}" "$@"
}
# Writes the bytes of the file $1 in pieces of 1, 3, 5, and 7 bytes, each after a pause, and then
# the rest.
pieces() {
  local n off=0 size
  size=$(stat -c %s "$1")
  for n in 1 3 5 7; do
    [ "$off" -lt "$size" ] || return 0
    sleep "${PAUSE:-0.2}"
    dd if="$1" bs=1 skip="$off" count="$n" status=none
    off=$((off + n))
  done
  [ "$off" -lt "$size" ] || return 0
  sleep "${PAUSE:-0.2}"
  tail -c +"$((off + 1))" "$1"
}
# Checks the run named $1 that ended with status $2 and wrote the file $3 against the status $4
# and the file $5.
check() {
  if [ "$2" -eq "$4" ] && cmp -s "$5" "$3"; then
    echo "pass: $1: status $2, $(stat -c %s "$3") bytes"
  else
    echo "fail: $1: status $2 where $4 is due, output $(head -c 32 "$3" | od -An -tx1)"
    status=1
  fi
}
: >"$out/empty"
# Runs the case whose message is $1 and whose output must be $2 with status $3, natively and
# under qemu-aarch64, from a file and from a pipe.
run_case() {
  local in=$1 want=$2 st=$3 name code
  name=$(basename "${in%.in}")
  for how in native qemu; do
    if [ "$how" = native ]; then set -- "$out/flip.elf"; else set -- "$qemu" "$out/flip.elf"; fi
    code=0
    scoped "$@" <"$in" >"$out/$name.$how.file" || code=$?
    check "$name $how from a file" "$code" "$out/$name.$how.file" "$st" "$want"
    code=0
    pieces "$in" | scoped "$@" >"$out/$name.$how.pipe" || code=$?
    check "$name $how from a pipe in pieces" "$code" "$out/$name.$how.pipe" "$st" "$want"
  done
}
for n in $(ls "$out" | sed -n 's/^flip-\([0-9]*\)\.in$/\1/p' | sort -n); do
  run_case "$out/flip-$n.in" "$out/flip-$n.want" 0
done
for in in "$out"/flipover-*.in; do
  run_case "$in" "$out/empty" 64
done
# The error paths, on the host's processor.
code=0
scoped "$out/flip.elf" <&- >"$out/closed-in.out" || code=$?
check "standard input closed" "$code" "$out/closed-in.out" 65 "$out/empty"
code=0
scoped "$out/flip.elf" <"$out" >"$out/dir-in.out" || code=$?
check "standard input a directory" "$code" "$out/dir-in.out" 65 "$out/empty"
code=0
scoped "$out/flip.elf" <"$out/flip-4096.in" >&- || code=$?
check "standard output closed" "$code" "$out/empty" 66 "$out/empty"
code=0
scoped "$out/flip.elf" <"$out/flip-4096.in" >/dev/full || code=$?
check "standard output /dev/full" "$code" "$out/empty" 66 "$out/empty"
code=0
(trap '' XFSZ; ulimit -f 64; exec "$out/flip.elf" <"$out/flip-1000000.in" >"$out/limit.out") ||
  code=$?
head -c "$(stat -c %s "$out/limit.out")" "$out/flip-1000000.want" >"$out/limit.want"
if [ "$(stat -c %s "$out/limit.out")" -lt 1000000 ]; then
  check "a file size limit of 64 blocks" "$code" "$out/limit.out" 66 "$out/limit.want"
else
  echo "fail: a file size limit of 64 blocks: the whole output was written"
  status=1
fi
code=0
set +o pipefail
scoped "$out/flip.elf" <"$out/flip-8800000.in" | head -c 100 >"$out/early.out"
code=${PIPESTATUS[0]}
set -o pipefail
if [ "$code" -eq 141 ]; then
  echo "pass: a reader that closes early: status 141, SIGPIPE"
else
  echo "fail: a reader that closes early: status $code"
  status=1
fi
exit "$status"
