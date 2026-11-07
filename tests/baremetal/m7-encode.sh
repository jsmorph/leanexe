#!/usr/bin/env bash
# The comparison of the Cortex-M7 encoder of LeanExe/M7/Encode.lean with the GNU assembler
# (tests/TestSupport/M7/Asm.lean).  It builds m7-encode, writes the assembly of the samples of
# every form, assembles it with AS for ARMv7E-M in Thumb state, requires that the object holds no
# relocation, so that the assembler resolved every branch, extracts its .text with OBJCOPY, and
# checks with m7-encode check that the assembler's halfwords of each sample are the encoder's and
# decode to the sample.  AS, OBJCOPY, and READELF name arm-none-eabi-as, arm-none-eabi-objcopy, and
# arm-none-eabi-readelf unless set.  The products lie in OUT, build/m7-encode unless set.
# Usage: tests/baremetal/m7-encode.sh
set -euo pipefail
[ "$#" -eq 0 ] || { echo "usage: tests/baremetal/m7-encode.sh" >&2; exit 2; }
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/m7-encode}")
as=${AS:-arm-none-eabi-as}
objcopy=${OBJCOPY:-arm-none-eabi-objcopy}
readelf=${READELF:-arm-none-eabi-readelf}
mkdir -p "$out"
tools/leanrun --timeout 30m lake --log-level error build m7-encode
tools/leanrun --timeout 30m lake env .lake/build/bin/m7-encode gen "$out/samples.s"
"$as" -march=armv7e-m -mthumb -o "$out/samples.o" "$out/samples.s"
if "$readelf" -r "$out/samples.o" | grep -q '^Relocation section'; then
  echo "fail: the object of the samples holds relocations"
  exit 1
fi
"$objcopy" -O binary -j .text "$out/samples.o" "$out/samples.bin"
tools/leanrun --timeout 30m lake env .lake/build/bin/m7-encode check "$out/samples.bin"
