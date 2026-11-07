#!/usr/bin/env bash
# The echo of cmsdkTick through the Cortex-M7 back end on QEMU's mps2-an500.  It builds m7-windows
# and the loop theorem of tests/TestSupport/M7/QemuLoop.lean, writes the image that
# tests/TestSupport/M7/Qemu.lean lays out with m7-windows qemu, and elaborates
# tests/TestSupport/M7/QemuFile.lean in the directory of the image under a memory cap of MEM, 12G
# unless set, so that the kernel checks that the file holds the image's bytes and the loop theorem
# holds of the file.  It requires that each theorem whose axioms that file prints depends on no
# axiom beyond propext, Classical.choice, and Quot.sound, and reports the check's elapsed time and
# peak memory.  It then runs the image in QEMU with UART0 on a Unix-domain socket, and
# tests/baremetal/uart_echo.py plays the far end of the UART and checks that each reply is the
# byte sent with bit 5 flipped, as tests/baremetal/req.sh does for the C path's echo.  QEMU names
# qemu-system-arm, UV names uv, and TIMEOUT, 120 unless set, bounds each wait of the host script in
# seconds.  The products lie in OUT, build/baremetal/m7-qemu unless set: the image, the check's
# output and times, QEMU's trace log echo.trace, the host script's line echo.echo, and the
# messages of uv and QEMU in echo.stderr.
# Usage: tests/baremetal/m7-qemu.sh
set -euo pipefail
[ "$#" -eq 0 ] || { echo "usage: tests/baremetal/m7-qemu.sh" >&2; exit 2; }
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/m7-qemu}")
qemu=${QEMU:-qemu-system-arm}
uv=${UV:-uv}
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build m7-windows TestSupport.M7.QemuLoop
tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows qemu "$out/echo-cmsdk-qemu.bin"
status=0
if /usr/bin/time -v tools/leanrun --timeout 30m --memory-high "${MEM:-12G}" lake env \
    sh -c 'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/M7/QemuFile.lean" \
    >"$out/qemu.check" 2>"$out/qemu.time"; then
  printed=$(grep -c 'axioms' "$out/qemu.check" || true)
  other=$(grep 'depends on axioms' "$out/qemu.check" | sed 's/.*\[\(.*\)\]$/\1/' | tr ',' '\n' |
    tr -d ' ' | grep -cvx 'propext\|Classical.choice\|Quot.sound' || true)
  if [ "$printed" = 7 ] && [ "$other" = 0 ]; then
    echo "pass: the kernel's check of echo-cmsdk-qemu.bin," \
      "$(stat -c %s "$out/echo-cmsdk-qemu.bin") bytes, and the loop theorem over it"
  else
    echo "fail: the axioms of the check: $(head -c 600 "$out/qemu.check")"
    status=1
  fi
else
  echo "fail: the kernel's check of echo-cmsdk-qemu.bin: $(head -c 600 "$out/qemu.check")"
  status=1
fi
grep -E "Elapsed \(wall|Maximum resident" "$out/qemu.time"
if "$uv" run "$root/tests/baremetal/uart_echo.py" --timeout "${TIMEOUT:-120}" "$out/echo.trace" \
    "$qemu" -M mps2-an500 -display none -monitor none -kernel "$out/echo-cmsdk-qemu.bin" \
    >"$out/echo.echo" 2>"$out/echo.stderr"; then
  echo "pass: echo-cmsdk-qemu: $(cat "$out/echo.echo")"
else
  echo "fail: echo-cmsdk-qemu: $(cat "$out/echo.echo" "$out/echo.stderr" | paste -sd' ' |
    head -c 400)"
  status=1
fi
exit "$status"
