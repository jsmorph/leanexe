#!/usr/bin/env bash
# The AArch64 back end's programs as arm64 Images that Lean writes whole (LeanExe/A64/Startup.lean),
# under QEMU's virt machine.  a64-programs emit writes each program's Image, NAME.img, with the
# bytes that the UART must show and the status with which the program must end.  Lean then
# elaborates tests/TestSupport/A64/ImageFiles.lean in the directory of those files, so that the
# kernel checks that each NAME.img holds the bytes that genImage gives and proves, for a boot state
# whose memory holds the file at imageBase, the run to PSCI SYSTEM_OFF with the program's output,
# with no axiom beyond propext, Classical.choice, and Quot.sound.  For each Image the script checks QEMU's loading of it
# with tests/baremetal/a64-loadcheck.sh, runs it with the machine, CPU, and 1 GiB of RAM of
# tests/baremetal/qemu.sh within TIMEOUT seconds, 120 unless set, and requires QEMU to exit with
# status 0, which PSCI SYSTEM_OFF gives, and the UART output to be the expected bytes followed by
# one byte, the status: 0 after the result's bytes, or the code of a trap with no byte before it.
# ACCEL selects the accelerator, as qemu.sh describes.  The products lie in OUT,
# build/baremetal/a64-images unless set.
# Usage: tests/baremetal/a64-images.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-images}")
source tests/baremetal/qemu.sh
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build a64-programs TestSupport.A64.Gcd \
  TestSupport.A64.Crc TestSupport.A64.Sha TestSupport.A64.Fold LeanExe.A64.File \
  LeanExe.A64.Proof.ImageTheorem
status=0
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-programs emit "$out" || status=1
if tools/leanrun --timeout 60m --memory-high 16G lake env sh -c 'cd "$1" && lean "$2"' sh "$out" \
    "$root/tests/TestSupport/A64/ImageFiles.lean" >"$out/images.check" 2>&1 &&
    [ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' \
      "$out/images.check")" = 5 ]; then
  echo "pass: the kernel's check of the Images"
else
  echo "fail: the kernel's check of the Images: $(head -c 600 "$out/images.check")"
  status=1
fi
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
