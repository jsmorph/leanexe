#!/usr/bin/env bash
# Builds the calculator's AArch64 Image, runs it under QEMU's virt machine, and compares its
# output with Node's BigInt.
#
# The script builds Demos.BignumCalc.BytesBare and has tests/bignum-calc/messages.mjs write each
# message, NAME.in, the length in eight bytes, the lowest first, and the message, with NAME.line,
# the line that Node's BigInt gives.  tests/bignum-calc/EmitImage.lean writes the Image,
# build/bignum-calc/image/bignum-calc.img, and tests/baremetal/a64-loadcheck.sh checks that QEMU
# places the file where the theorems assume it.  With --check, Lean elaborates
# Demos/BignumCalc/Image.lean in the directory of the Image, whose kernel check compares the file
# with the generator's bytes and proves the Image's theorems, and the script requires eleven
# axiom reports with no axiom beyond propext, Classical.choice, and Quot.sound.  The check runs
# under tools/leanrun with the memory high limit MEM, 28G unless set; on an AArch64 host it took
# 151 s and a peak of 24.9 GiB.  Its time and peak resident size go to Image.time.
#
# QEMU runs the Image with the machine, CPU, and 1 GiB of RAM of tests/baremetal/qemu.sh, with the
# UART on a file backend whose input file holds a run's bytes.  QEMU must exit with status 0, and
# the UART must show the run's bytes:
#   each message        its line and the status 0, and one message also from a pipe in pieces
#   longer than 65,536  the status 64 alone
#   emptymsg            the length 0: the line 4 and the status 0
#   largest             the length 2^64 - 1: the status 64 alone
# A last run starts QEMU stopped, sends a break through QEMU's monitor into the empty receiver,
# and continues: the UART must show the status 65 alone.  ACCEL selects QEMU's accelerator, as
# qemu.sh describes, IMAGE_COUNT, when set, keeps the first IMAGE_COUNT messages, and each run
# must end within TIMEOUT seconds, 120 unless set.
# Usage: tests/bignum-calc/image.sh [--check]
set -euo pipefail
check=0
case "${1:-}" in
  --check) check=1 ;;
  "") ;;
  *)
    echo "usage: tests/bignum-calc/image.sh [--check]" >&2
    exit 2
    ;;
esac
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
host=tests/bignum-calc
out=build/bignum-calc/image

tools/leanrun --timeout 3h lake build Demos.BignumCalc.BytesBare
mkdir -p "$out"
msgs=$out/messages
rm -rf "$msgs"
node "$host/messages.mjs" "$msgs" ${IMAGE_COUNT:-}
tools/leanrun --timeout 30m lake env lean --run "$host/EmitImage.lean" "$out/bignum-calc.img"

status=0
if [ "$check" = 1 ]; then
  if /usr/bin/time -f '%e s, %M KB' -o "$out/Image.time" tools/leanrun --timeout 1h \
      --memory-high "${MEM:-28G}" lake env sh -c 'cd "$1" && lean "$2"' sh "$out" \
      "$root/Demos/BignumCalc/Image.lean" >"$out/Image.check" 2>&1 &&
      [ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' \
        "$out/Image.check")" = 11 ]; then
    echo "pass: the kernel's check of Image.lean, $(cat "$out/Image.time")"
  else
    echo "fail: the kernel's check of Image.lean: $(head -c 600 "$out/Image.check")"
    status=1
  fi
fi

tests/baremetal/a64-loadcheck.sh "$out/bignum-calc.img"
source tests/baremetal/qemu.sh
img=$out/bignum-calc.img
cases=$out/cases
rm -rf "$cases"
mkdir -p "$cases"

# Runs the Image with the remaining arguments.
run() {
  timeout "${TIMEOUT:-120}" "$qemu" -M virt "${bm_cpu[@]}" -m 1G -display none "$@" -kernel "$img"
}
# Writes the bytes of the file $1 in pieces of 1, 3, 5, and 7 bytes, each after a pause of 0.2 s,
# and then the rest.
pieces() {
  local n off=0
  for n in 1 3 5 7; do
    sleep 0.2
    dd if="$1" bs=1 skip="$off" count="$n" status=none
    off=$((off + n))
  done
  sleep 0.2
  tail -c +"$((off + 1))" "$1"
}
# Runs the case whose files are $1.in and $1.want from a file backend.
run_case() {
  local base=$1 qcode=0
  run -monitor none -chardev "file,id=u0,path=$base.file,input-path=$base.in" \
    -serial chardev:u0 </dev/null || qcode=$?
  if [ "$qcode" -ne 0 ] || ! cmp -s "$base.want" "$base.file"; then
    echo "fail: $(basename "$base"): QEMU status $qcode, output $(od -An -c "$base.file" | head -c 300)"
    status=1
  fi
}

names=()
over=0
for in in "$msgs"/*.in; do
  name=$(basename "${in%.in}")
  cp "$in" "$cases/$name.in"
  if [ "$(($(stat -c %s "$in") - 8))" -gt 65536 ]; then
    printf '\100' >"$cases/$name.want"
    over=$((over + 1))
  else
    { cat "${in%.in}.line"; printf '\0'; } >"$cases/$name.want"
  fi
  names+=("$name")
done
printf '\0\0\0\0\0\0\0\0' >"$cases/emptymsg.in"
printf '4\0' >"$cases/emptymsg.want"
printf '\377\377\377\377\377\377\377\377' >"$cases/largest.in"
printf '\100' >"$cases/largest.want"
for name in "${names[@]}" emptymsg largest; do
  run_case "$cases/$name"
done

piece=${names[0]}
qcode=0
pieces "$cases/$piece.in" | run -monitor none -serial stdio >"$cases/pipe.out" || qcode=$?
if [ "$qcode" -ne 0 ] || ! cmp -s "$cases/$piece.want" "$cases/pipe.out"; then
  echo "fail: $piece from a pipe: QEMU status $qcode"
  status=1
else
  echo "pass: $piece from a pipe in pieces"
fi

: >"$cases/none.in"
printf '\101' >"$cases/break.want"
qcode=0
printf 'chardev-send-break u0\ncont\n' | run -S -monitor stdio \
  -chardev "file,id=u0,path=$cases/break.file,input-path=$cases/none.in" -serial chardev:u0 \
  >"$cases/break.monitor" || qcode=$?
if [ "$qcode" -ne 0 ] || ! cmp -s "$cases/break.want" "$cases/break.file"; then
  echo "fail: a break: QEMU status $qcode, output $(od -An -tx1 "$cases/break.file")"
  status=1
else
  echo "pass: a break gives the status 65"
fi

if [ "$status" = 0 ]; then
  echo "aarch64 ($accel): the Image's output on ${#names[@]} messages equals Node's BigInt line," \
    "each followed by the status 0, except $over longer than 65,536 bytes with the status 64" \
    "alone; the empty message gives the line 4 and the length 2^64 - 1 the status 64"
fi
exit "$status"
