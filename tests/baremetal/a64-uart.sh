#!/usr/bin/env bash
# The AArch64 images that read their input from the UART under QEMU's virt machine: GCD's loop of
# tests/TestSupport/A64/Uart.lean, which reads two words, and the flip of bit 5 of each byte of
# tests/TestSupport/A64/Flip.lean, which reads a length of eight bytes and the message.  a64-uart
# emit writes the Images, gcduart.img and flip.img, and for each case the bytes that the UART
# delivers and the bytes that it must show.  Lean then elaborates
# tests/TestSupport/A64/ImageFilesUart.lean and tests/TestSupport/A64/ImageFilesFlip.lean in the
# directory of those files with a MemoryHigh of 8G, so that the kernel checks that each Image file
# holds the bytes that its generator gives and proves the Images' theorems, with no axiom beyond
# propext, Classical.choice, and Quot.sound.  The script checks QEMU's loading of each Image with
# tests/baremetal/a64-loadcheck.sh and runs it with the machine, CPU, and 1 GiB of RAM of
# tests/baremetal/qemu.sh, each run within TIMEOUT seconds, 120 unless set.  On each case it runs
# the Image twice: with the UART on a file backend whose input file holds the case's bytes, and
# with the UART on QEMU's standard input and output, a pipe into which the script writes the bytes
# in pieces of 1, 3, 5, and 7 bytes, each after a pause of PAUSE seconds, 0.2 unless set, and then
# the rest at once.  QEMU must exit with status 0, and the UART must show the case's bytes: the
# GCD's eight bytes and the status 0, the flipped message and the status 0, or the status 64 for a
# length above the flip's limit.  A last run of each Image starts QEMU stopped, sends a break on
# the UART through QEMU's monitor, which puts a word with the break flag in the receiver, and
# continues: the UART must show the status 65 alone.  ACCEL selects the accelerator, as qemu.sh
# describes.  The products lie in OUT, build/baremetal/a64-uart unless set.
# Usage: tests/baremetal/a64-uart.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-uart}")
source tests/baremetal/qemu.sh
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build a64-uart \
  TestSupport.A64.Uart TestSupport.A64.Flip LeanExe.A64.File
status=0
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-uart emit "$out" || status=1
# Elaborates the module $1 of tests/TestSupport/A64 in the directory of the Images and requires
# $2 theorems with the standard axioms.
kernel_check() {
  if tools/leanrun --timeout 60m --memory-high 8G lake env sh -c 'cd "$1" && lean "$2"' sh "$out" \
      "$root/tests/TestSupport/A64/$1.lean" >"$out/$1.check" 2>&1 &&
      [ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' \
        "$out/$1.check")" = "$2" ]; then
    echo "pass: the kernel's check of $1.lean"
  else
    echo "fail: the kernel's check of $1.lean: $(head -c 600 "$out/$1.check")"
    status=1
  fi
}
kernel_check ImageFilesUart 5
kernel_check ImageFilesFlip 4
for img in "$out/gcduart.img" "$out/flip.img"; do
  if ! check=$(tests/baremetal/a64-loadcheck.sh "$img"); then
    echo "$check"
    exit 1
  fi
done
# Runs the Image $1 with the remaining arguments.
run() {
  local img=$1
  shift
  timeout "${TIMEOUT:-120}" "$qemu" -M virt "${bm_cpu[@]}" -m 1G -display none "$@" \
    -kernel "$img"
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
# Runs the Image $1 on the case whose files are $2.in and $2.want, from a file and from a pipe.
run_case() {
  local img=$1 base=$2 name qcode
  name=$(basename "$base")
  qcode=0
  run "$img" -monitor none -chardev "file,id=u0,path=$base.file,input-path=$base.in" \
    -serial chardev:u0 </dev/null || qcode=$?
  if [ "$qcode" -ne 0 ] || ! cmp -s "$base.want" "$base.file"; then
    echo "fail: $name from a file: QEMU status $qcode, output $(head -c 64 "$base.file" |
      od -An -tx1)"
    status=1
  else
    echo "pass: $name from a file: $(stat -c %s "$base.want") bytes, the last" \
      "$(tail -c 1 "$base.want" | od -An -tx1 | tr -d ' ')"
  fi
  qcode=0
  pieces "$base.in" | run "$img" -monitor none -serial stdio >"$base.pipe" || qcode=$?
  if [ "$qcode" -ne 0 ] || ! cmp -s "$base.want" "$base.pipe"; then
    echo "fail: $name from a pipe: QEMU status $qcode, output $(head -c 64 "$base.pipe" |
      od -An -tx1)"
    status=1
  else
    echo "pass: $name from a pipe in pieces"
  fi
}
for in in "$out"/gcduart-*.in; do
  run_case "$out/gcduart.img" "${in%.in}"
done
for n in $(ls "$out" | sed -n 's/^flip-\([0-9]*\)\.in$/\1/p' | sort -n); do
  run_case "$out/flip.img" "$out/flip-$n"
done
for in in "$out"/flipover-*.in; do
  run_case "$out/flip.img" "${in%.in}"
done
: >"$out/empty.in"
printf '\x41' >"$out/break.want"
for img in gcduart flip; do
  qcode=0
  printf 'chardev-send-break u0\ncont\n' | run "$out/$img.img" -S -monitor stdio \
    -chardev "file,id=u0,path=$out/$img-break.file,input-path=$out/empty.in" -serial chardev:u0 \
    >"$out/$img-break.monitor" || qcode=$?
  if [ "$qcode" -ne 0 ] || ! cmp -s "$out/break.want" "$out/$img-break.file"; then
    echo "fail: a break on $img: QEMU status $qcode, output $(od -An -tx1 "$out/$img-break.file")"
    status=1
  else
    echo "pass: a break on $img gives status 65"
  fi
done
exit "$status"
