#!/usr/bin/env bash
# The programs with requests through the Cortex-M7 back end on QEMU's mps2-an500: the echo of
# cmsdkTick, NAME echo, the default, the energy controller's gateway of gwTick, NAME gateway, the
# CRC-32 step crcCmsdkTick, NAME crc, the SHA-256 step shaCmsdkTick, NAME sha, the signed step
# sgCmsdkTick, NAME signed, the echo of records dlCmsdkTick, NAME delim, and the BMS step bmsTick,
# NAME bms.  It builds m7-windows and the loop theorem of tests/TestSupport/M7/QemuLoop.lean,
# GwLoop.lean, CrcLoop.lean, ShaLoop.lean, SignedLoop.lean, DelimLoop.lean, or BmsLoop.lean, and
# writes the image that tests/TestSupport/M7/Qemu.lean, GwImages.lean, CrcImages.lean,
# ShaImages.lean, SignedImages.lean, DelimImages.lean, or BmsImages.lean lays out with m7-windows
# qemu, gateway-qemu, crc-qemu, sha-qemu, signed-qemu, delim-qemu, or bms-qemu.  It elaborates
# tests/TestSupport/M7/QemuFile.lean, GwQemuFile.lean, CrcQemuFile.lean, ShaQemuFile.lean,
# SignedQemuFile.lean, DelimQemuFile.lean, or BmsQemuFile.lean in the directory of the image under
# a memory cap of MEM, 24G for the BMS step, 16G for the gateway, the SHA-256 step, and the echo of
# records, and 12G otherwise unless set, so
# that the kernel checks that the file holds the image's bytes, the gateway's in parts, and the
# loop theorem holds of the file.  It requires that each theorem whose axioms that file prints
# depends on no axiom beyond propext, Classical.choice, and Quot.sound, and reports the check's
# elapsed time and peak memory.
#
# It then runs the image in QEMU with UART0 on a Unix-domain socket and plays the far end of the
# UART, as tests/baremetal/req.sh does for the C path's programs.  For the echo,
# tests/baremetal/uart_echo.py checks that each reply is the byte sent with bit 5 flipped, for
# CRC-32, tests/baremetal/uart_crc.py that each reply is the low byte of zlib.crc32 of the bytes
# sent so far, for SHA-256, tests/baremetal/uart_sha.py that each answer to a block of 64 bytes
# is hashlib.sha256 of the bytes sent so far, for the signed step,
# tests/baremetal/uart_signed.py that each reply is its model's of the step's integrator, and for
# the echo of records, tests/baremetal/uart_delim.py that each answer to a segment is that of the
# mirror of the delimited framing in tests/baremetal/delim_frame.py.  For the BMS step,
# tests/baremetal/uart_bms.py runs the fault-injection schedule without the board resets, which
# QEMU's UART cannot make, writes the bytes of both directions to bms.in and bms.out, and checks
# each answer against its Python mirror and the schedule, and bms-replay then checks every answer
# of bms.out against the machine of Demos/Bms/Spec.lean.  For the
# gateway, tests/baremetal/uart_gateway.py simulates TICKS minutes, 10,080 unless set, of the
# plant of the minute series SERIES, $HOME/data/energy/series/nist-2015.csv unless set, and checks
# the commands and the monitoring, and native-bare gateway-run then runs the gateway in native
# Lean on the same input records, whose output records must equal the image's.  QEMU names
# qemu-system-arm, UV names uv, and TIMEOUT, 120 unless set, bounds each wait of the host script in
# seconds.  The products lie in OUT, build/baremetal/m7-qemu unless set: the image, the check's
# output and times, QEMU's trace log NAME.trace, the host script's line NAME.echo, the messages of
# uv and QEMU in NAME.stderr, for the gateway the records gateway.records.in,
# gateway.records.out, and gateway.records.lean, and for the BMS step the logs bms.in, bms.out,
# and bms.log of uart_bms.py and the replay's line bms.replay.
# Usage: tests/baremetal/m7-qemu.sh [echo | gateway | crc | sha | signed | delim | bms]
set -euo pipefail
usage() {
  echo "usage: tests/baremetal/m7-qemu.sh [echo | gateway | crc | sha | signed | delim | bms]" >&2
  exit 2
}
[ "$#" -le 1 ] || usage
name=${1:-echo}
case $name in
  echo) image=echo-cmsdk-qemu cmd=qemu lib=TestSupport.M7.QemuLoop file=QemuFile count=7
    mem=${MEM:-12G} ;;
  gateway) image=gateway-cmsdk-qemu cmd=gateway-qemu lib=TestSupport.M7.GwLoop file=GwQemuFile
    count=5 mem=${MEM:-16G} ;;
  crc) image=crc-cmsdk-qemu cmd=crc-qemu lib=TestSupport.M7.CrcLoop file=CrcQemuFile count=6
    mem=${MEM:-12G} ;;
  sha) image=sha-cmsdk-qemu cmd=sha-qemu lib=TestSupport.M7.ShaLoop file=ShaQemuFile count=7
    mem=${MEM:-16G} ;;
  signed) image=signed-cmsdk-qemu cmd=signed-qemu lib=TestSupport.M7.SignedLoop
    file=SignedQemuFile count=4 mem=${MEM:-12G} ;;
  delim) image=delim-cmsdk-qemu cmd=delim-qemu lib=TestSupport.M7.DelimLoop
    file=DelimQemuFile count=11 mem=${MEM:-16G} ;;
  bms) image=bms-cmsdk-qemu cmd=bms-qemu lib=TestSupport.M7.BmsLoop file=BmsQemuFile count=8
    mem=${MEM:-24G} ;;
  *) usage ;;
esac
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/m7-qemu}")
qemu=${QEMU:-qemu-system-arm}
uv=${UV:-uv}
series=${SERIES:-$HOME/data/energy/series/nist-2015.csv}
mkdir -p "$out"
rm -f "${out:?}/$name".* "${out:?}/$image".* "${out:?}/$file".*
targets=(m7-windows "$lib")
[ "$name" = gateway ] && targets+=(native-bare)
[ "$name" = bms ] && targets+=(bms-replay)
tools/leanrun --timeout 60m --memory-high "$mem" lake --log-level error build "${targets[@]}"
tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows "$cmd" "$out/$image.bin"
status=0
if /usr/bin/time -v tools/leanrun --timeout 30m --memory-high "$mem" lake env \
    sh -c 'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/M7/$file.lean" \
    >"$out/$file.check" 2>"$out/$file.time"; then
  printed=$(grep -c 'axioms' "$out/$file.check" || true)
  other=$(grep 'depends on axioms' "$out/$file.check" | sed 's/.*\[\(.*\)\]$/\1/' | tr ',' '\n' |
    tr -d ' ' | grep -cvx 'propext\|Classical.choice\|Quot.sound' || true)
  if [ "$printed" = "$count" ] && [ "$other" = 0 ]; then
    echo "pass: the kernel's check of $image.bin, $(stat -c %s "$out/$image.bin") bytes," \
      "and the loop theorem over it"
  else
    echo "fail: the axioms of the check: $(head -c 600 "$out/$file.check")"
    status=1
  fi
else
  echo "fail: the kernel's check of $image.bin: $(head -c 600 "$out/$file.check")"
  status=1
fi
grep -E "Elapsed \(wall|Maximum resident" "$out/$file.time"
case $name in
  echo) host=(uart_echo.py) ;;
  crc) host=(uart_crc.py) ;;
  sha) host=(uart_sha.py) ;;
  signed) host=(uart_signed.py) ;;
  delim) host=(uart_delim.py) ;;
  bms) host=(uart_bms.py qemu --timeout "${TIMEOUT:-120}" "$out/bms") ;;
  gateway) host=(uart_gateway.py --ticks "${TICKS:-10080}" "$series" "$out/$name.records") ;;
esac
[ "$name" = bms ] || host=("${host[0]}" --timeout "${TIMEOUT:-120}" "${host[@]:1}")
if "$uv" run "$root/tests/baremetal/${host[0]}" "${host[@]:1}" \
    "$out/$name.trace" "$qemu" -M mps2-an500 -display none -monitor none \
    -kernel "$out/$image.bin" >"$out/$name.echo" 2>"$out/$name.stderr"; then
  echo "pass: $image: $(cat "$out/$name.echo")"
else
  echo "fail: $image: $(cat "$out/$name.echo" "$out/$name.stderr" | paste -sd' ' | head -c 400)"
  exit 1
fi
if [ "$name" = gateway ]; then
  if ! tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare gateway-run \
      "$out/$name.records.in" "$out/$name.records.lean" >"$out/$name.native" 2>&1; then
    echo "fail: $image: native-bare gateway-run failed:" \
      "$(paste -sd' ' "$out/$name.native" | head -c 400)"
    exit 1
  fi
  if cmp -s "$out/$name.records.out" "$out/$name.records.lean"; then
    echo "pass: $image: the output records equal native Lean's for" \
      "$(wc -l <"$out/$name.records.in") input records"
  else
    echo "fail: $image: the output records differ from native Lean's:" \
      "$(cmp "$out/$name.records.out" "$out/$name.records.lean" 2>&1 | head -c 300)"
    status=1
  fi
fi
if [ "$name" = bms ]; then
  if tools/leanrun --timeout 30m lake env .lake/build/bin/bms-replay "$out/bms" \
      >"$out/bms.replay" 2>&1; then
    echo "pass: $image: $(cat "$out/bms.replay")"
  else
    echo "fail: $image: $(paste -sd' ' "$out/bms.replay" | head -c 400)"
    status=1
  fi
fi
exit "$status"
