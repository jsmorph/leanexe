#!/usr/bin/env bash
# The AArch64 back end's programs as arm64 Images that Lean writes whole (LeanExe/A64/Startup.lean),
# under QEMU's virt machine.  a64-programs emit writes each program's Image, NAME.img, with the
# bytes that the UART must show and the status with which the program must end.  For each Image the
# script checks QEMU's loading of it with tests/baremetal/a64-loadcheck.sh, runs it with the
# machine, CPU, and 1 GiB of RAM of tests/baremetal/qemu.sh within TIMEOUT seconds, 120 unless set,
# and requires QEMU to exit with status 0, which PSCI SYSTEM_OFF gives, and the UART output to be
# the expected bytes followed by one byte, the status: 0 after the result's bytes, or the code of a
# trap with no byte before it.  ACCEL selects the accelerator, as qemu.sh describes.  The products
# lie in OUT, build/baremetal/a64-images unless set.
# Usage: tests/baremetal/a64-images.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-images}")
source tests/baremetal/qemu.sh
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build a64-programs
status=0
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-programs emit "$out" || status=1
for img in "$out"/*.img; do
  name=$(basename "${img%.img}")
  if ! check=$(tests/baremetal/a64-loadcheck.sh "$img"); then
    echo "$check"
    status=1
    continue
  fi
  want=$(cat "$out/$name.status")
  cp "$out/$name.expected" "$out/$name.want"
  printf "\\x$(printf %02x "$want")" >>"$out/$name.want"
  qcode=0
  timeout "${TIMEOUT:-120}" "$qemu" -M virt "${bm_cpu[@]}" -m 1G -display none -monitor none \
    -serial "file:$out/$name.serial" -kernel "$img" </dev/null || qcode=$?
  if [ "$qcode" -ne 0 ] || ! cmp -s "$out/$name.want" "$out/$name.serial"; then
    echo "fail: $name: QEMU status $qcode, output $(od -An -tx1 "$out/$name.serial" | head -c 200)"
    status=1
  else
    echo "pass: $name: $(stat -c %s "$img") bytes, output $(stat -c %s "$out/$name.serial") bytes"
  fi
done
exit "$status"
