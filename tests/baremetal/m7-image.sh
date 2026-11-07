#!/usr/bin/env bash
# The kernel's checks of the Cortex-M7 code of the echo and of the gateway.  It builds m7-windows,
# the step theorems of tests/TestSupport/M7/Step.lean and GwStep.lean, and the parts' theorems of
# LeanExe/M7/Proof/Parts.lean, writes the bytes of the programs that LeanExe/M7/Gen.lean generates
# for usart3Tick and gwTickUsart3 with m7-windows image, and elaborates
# tests/TestSupport/M7/ImageFile.lean and GwImageFile.lean in the directory of those files, so that
# the kernel checks that each file holds the generated instructions' bytes, the gateway's in parts.
# A memory cap of MEM, 16G unless set, bounds the build and each check.  It requires that the
# checks, the step theorems, and the parts' theorems depend on no axiom beyond propext,
# Classical.choice, and Quot.sound, and reports each check's elapsed time and peak memory.  The
# products lie in OUT, build/baremetal/m7-image unless set.
# Usage: tests/baremetal/m7-image.sh
set -euo pipefail
[ "$#" -eq 0 ] || { echo "usage: tests/baremetal/m7-image.sh" >&2; exit 2; }
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/m7-image}")
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m --memory-high "${MEM:-16G}" lake --log-level error build m7-windows \
  TestSupport.M7.Step TestSupport.M7.GwStep TestSupport.M7.Windows LeanExe.M7.Proof.Parts
status=0
# check NAME FILE COUNT: writes program NAME to NAME.bin, elaborates FILE.lean beside it, and
# requires COUNT lines that name the three axioms alone.
check() {
  tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows image "$1" "$out/$1.bin"
  if /usr/bin/time -v tools/leanrun --timeout 30m --memory-high "${MEM:-16G}" lake env \
      sh -c 'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/M7/$2.lean" \
      >"$out/$2.check" 2>"$out/$2.time" &&
      [ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' \
        "$out/$2.check")" = "$3" ]; then
    echo "pass: the kernel's check of $1.bin, $(stat -c %s "$out/$1.bin") bytes"
  else
    echo "fail: the kernel's check of $1.bin: $(head -c 600 "$out/$2.check")"
    status=1
  fi
  grep -E "Elapsed \(wall|Maximum resident" "$out/$2.time"
}
check echo-usart3 ImageFile 5
check gateway-usart3 GwImageFile 7
exit "$status"
