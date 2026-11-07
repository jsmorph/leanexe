#!/usr/bin/env bash
# The kernel's check of the Cortex-M7 echo's code.  It builds m7-windows and the step theorems of
# tests/TestSupport/M7/Step.lean, writes the bytes of the program that LeanExe/M7/Gen.lean
# generates for usart3Tick with m7-windows image echo-usart3, and elaborates
# tests/TestSupport/M7/ImageFile.lean in the directory of that file under a memory cap of MEM, 12G
# unless set, so that the kernel checks that the file holds the generated instructions' bytes.  It
# requires that the check and the step theorems depend on no axiom beyond propext,
# Classical.choice, and Quot.sound, and reports the check's elapsed time and peak memory.  The
# products lie in OUT, build/baremetal/m7-image unless set.
# Usage: tests/baremetal/m7-image.sh
set -euo pipefail
[ "$#" -eq 0 ] || { echo "usage: tests/baremetal/m7-image.sh" >&2; exit 2; }
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/m7-image}")
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build m7-windows TestSupport.M7.Step \
  TestSupport.M7.Windows
tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows image echo-usart3 \
  "$out/echo-usart3.bin"
status=0
if /usr/bin/time -v tools/leanrun --timeout 30m --memory-high "${MEM:-12G}" lake env \
    sh -c 'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/M7/ImageFile.lean" \
    >"$out/image.check" 2>"$out/image.time" &&
    [ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' \
      "$out/image.check")" = 5 ]; then
  echo "pass: the kernel's check of echo-usart3.bin, $(stat -c %s "$out/echo-usart3.bin") bytes"
else
  echo "fail: the kernel's check of echo-usart3.bin: $(head -c 600 "$out/image.check")"
  status=1
fi
grep -E "Elapsed \(wall|Maximum resident" "$out/image.time"
exit "$status"
