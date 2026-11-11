#!/usr/bin/env bash
# The comparison of the AArch64 encoder of LeanExe/A64/Encode.lean with the GNU assembler for the
# loads LDR Wt and LDRB (tests/TestSupport/A64/Asm.lean).  It builds a64-encode, writes the
# assembly of the samples, assembles it with AS, requires that the object holds no relocation,
# extracts its .text with OBJCOPY, and checks with a64-encode check that the assembler's word of
# each sample is the encoder's and decodes to the sample.  AS, OBJCOPY, and READELF name as,
# objcopy, and readelf unless set, the native tools of an AArch64 host.  The products lie in OUT,
# build/a64-encode unless set.
# Usage: tests/baremetal/a64-encode.sh
set -euo pipefail
[ "$#" -eq 0 ] || { echo "usage: tests/baremetal/a64-encode.sh" >&2; exit 2; }
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/a64-encode}")
as=${AS:-as}
objcopy=${OBJCOPY:-objcopy}
readelf=${READELF:-readelf}
mkdir -p "$out"
tools/leanrun --timeout 30m lake --log-level error build a64-encode
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-encode gen "$out/samples.s"
"$as" -o "$out/samples.o" "$out/samples.s"
if "$readelf" -r "$out/samples.o" | grep -q '^Relocation section'; then
  echo "fail: the object of the samples holds relocations"
  exit 1
fi
"$objcopy" -O binary -j .text "$out/samples.o" "$out/samples.bin"
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-encode check "$out/samples.bin"
