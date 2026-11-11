#!/usr/bin/env bash
# The AArch64 image that reads its arguments from the UART, GCD's loop of
# tests/TestSupport/A64/Uart.lean, under QEMU's virt machine.  a64-uart emit writes the Image,
# gcduart.img, and for each pair of words of TestSupport.A64.Uart.cases the bytes that the UART
# delivers and the bytes that it must show.  Lean then elaborates
# tests/TestSupport/A64/ImageFilesUart.lean in the directory of those files with a MemoryHigh of 8G,
# so that the kernel checks that gcduart.img holds the bytes that genInImage gives and proves the
# Image's theorems, with no axiom beyond propext, Classical.choice, and Quot.sound.  The script
# checks QEMU's loading of the Image with tests/baremetal/a64-loadcheck.sh and runs it with the
# machine, CPU, and 1 GiB of RAM of tests/baremetal/qemu.sh, each run within TIMEOUT seconds, 120
# unless set.  On each pair it runs the Image twice: with the UART on a file backend whose input
# file holds the pair's sixteen bytes, and with the UART on QEMU's standard input and output, a pipe
# into which the script writes the bytes in pieces of 1, 3, 5, and 7 bytes, each after a pause of
# PAUSE seconds, 0.2 unless set.  QEMU must exit with status 0, and the UART must show the GCD's
# eight bytes and the status 0.  A last run starts QEMU stopped, sends a break on the UART through
# QEMU's monitor, which puts a word with the break flag in the receiver, and continues: the UART
# must show the status 65 alone.  ACCEL selects the accelerator, as qemu.sh describes.  The products
# lie in OUT, build/baremetal/a64-uart unless set.
# Usage: tests/baremetal/a64-uart.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-uart}")
source tests/baremetal/qemu.sh
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build a64-uart \
  TestSupport.A64.Uart LeanExe.A64.File
status=0
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-uart emit "$out" || status=1
if tools/leanrun --timeout 60m --memory-high 8G lake env sh -c 'cd "$1" && lean "$2"' sh "$out" \
    "$root/tests/TestSupport/A64/ImageFilesUart.lean" >"$out/ImageFilesUart.check" 2>&1 &&
    [ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' \
      "$out/ImageFilesUart.check")" = 3 ]; then
  echo "pass: the kernel's check of ImageFilesUart.lean"
else
  echo "fail: the kernel's check of ImageFilesUart.lean: $(head -c 600 "$out/ImageFilesUart.check")"
  status=1
fi
img=$out/gcduart.img
if ! check=$(tests/baremetal/a64-loadcheck.sh "$img"); then
  echo "$check"
  exit 1
fi
run() {
  timeout "${TIMEOUT:-120}" "$qemu" -M virt "${bm_cpu[@]}" -m 1G -display none "$@" \
    -kernel "$img"
}
# Writes the bytes of the file $1 in pieces of 1, 3, 5, and 7 bytes, each after a pause.
pieces() {
  local n off=0 size
  size=$(stat -c %s "$1")
  for n in 1 3 5 7; do
    sleep "${PAUSE:-0.2}"
    dd if="$1" bs=1 skip="$off" count="$n" status=none
    off=$((off + n))
  done
  [ "$off" -eq "$size" ] || { echo "the pieces do not cover $1" >&2; return 1; }
}
for in in "$out"/gcduart-*.in; do
  name=$(basename "${in%.in}")
  want=$out/$name.want
  qcode=0
  run -monitor none -chardev "file,id=u0,path=$out/$name.file,input-path=$in" \
    -serial chardev:u0 </dev/null || qcode=$?
  if [ "$qcode" -ne 0 ] || ! cmp -s "$want" "$out/$name.file"; then
    echo "fail: $name from a file: QEMU status $qcode, output $(od -An -tx1 "$out/$name.file")"
    status=1
  else
    echo "pass: $name from a file: $(od -An -tx1 "$want" | tr -s ' ')"
  fi
  qcode=0
  pieces "$in" | run -monitor none -serial stdio >"$out/$name.pipe" || qcode=$?
  if [ "$qcode" -ne 0 ] || ! cmp -s "$want" "$out/$name.pipe"; then
    echo "fail: $name from a pipe: QEMU status $qcode, output $(od -An -tx1 "$out/$name.pipe")"
    status=1
  else
    echo "pass: $name from a pipe in pieces"
  fi
done
: >"$out/empty.in"
printf '\x41' >"$out/break.want"
qcode=0
printf 'chardev-send-break u0\ncont\n' | run -S -monitor stdio \
  -chardev "file,id=u0,path=$out/break.file,input-path=$out/empty.in" -serial chardev:u0 \
  >"$out/break.monitor" || qcode=$?
if [ "$qcode" -ne 0 ] || ! cmp -s "$out/break.want" "$out/break.file"; then
  echo "fail: a break: QEMU status $qcode, output $(od -An -tx1 "$out/break.file")"
  status=1
else
  echo "pass: a break gives status 65"
fi
exit "$status"
