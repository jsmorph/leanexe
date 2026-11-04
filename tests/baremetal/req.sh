#!/usr/bin/env bash
# The echo of the request protocol (tests/TestSupport/Bare/Req.lean) on QEMU's mps2-an500, a
# Cortex-M7.  native-bare emit-req writes each program's C text, the translation of its module
# followed by the main that runs the step forever and performs each request with a volatile 32-bit
# load or store of lx_reg, and the names of the functions that take the call depth.  The ARMv7-M
# tree's clightgen reads each C text back, and native-bare check-req compares the whole program
# with the program of the theorem.  Given DIR, the script skips these steps and takes NAME.c and
# NAME.depth from DIR, as an earlier run wrote them.
#
# Each program NAME is built with tools/baremetal/armv7m/build.sh, whose stack bound and access
# check must hold, and whose linker script places lx_reg at the registers of UART0.
# tests/baremetal/uart_echo.py then runs it in QEMU with UART0 on a socket, plays the far end of
# the UART, checks that each reply is the byte sent with bit 5 flipped, as cmsdkTick computes, and
# stops QEMU.  The products lie in OUT, build/baremetal/req unless set: NAME.elf with the files of
# build.sh, NAME.trace, QEMU's log, NAME.echo, the line that uart_echo.py prints, and NAME.stderr,
# the messages of uv and QEMU.  CCOMP, CCOMP_STDLIB, and CLIGHTGEN name CompCert 3.18's driver,
# run-time library, and clightgen configured armv7m-eabihf, QEMU names qemu-system-arm, OBJDUMP
# and NM name objdump and nm for ARM, UV names uv, and TIMEOUT, 120 unless set, bounds each wait
# of uart_echo.py in seconds.
# Usage: tests/baremetal/req.sh [DIR]
set -euo pipefail
if [ "$#" -gt 1 ]; then
  echo "usage: tests/baremetal/req.sh [DIR]" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
here=$root/tests/baremetal
tools=$root/tools/baremetal/armv7m
out=${OUT:-$root/build/baremetal/req}
clightgen=${CLIGHTGEN:-clightgen}
qemu=${QEMU:-qemu-system-arm}
uv=${UV:-uv}
dir=$out
if [ "$#" -eq 1 ]; then
  dir=$(cd "$1" && pwd)
fi
rm -rf "$out"
mkdir -p "$out"

if [ "$#" -eq 0 ]; then
  cd "$root"
  tools/leanrun --timeout 60m lake --log-level error build native-bare
  tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare emit-req "$out"
  for c in "$out"/*.c; do
    (cd "$out" && "$clightgen" "$(basename "$c")")
  done
  tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare check-req "$out"
fi

status=0
for c in "$dir"/*.c; do
  name=$(basename "${c%.c}")
  if ! STACK_DEPTHS=$dir/$name.depth "$tools/build.sh" "$out/$name.elf" "$c" \
      >"$out/$name.build" 2>&1; then
    echo "fail: $name: $(paste -sd' ' "$out/$name.build" | head -c 400)"
    status=1
    continue
  fi
  if "$uv" run "$here/uart_echo.py" --timeout "${TIMEOUT:-120}" "$out/$name.trace" "$qemu" \
      -M mps2-an500 -display none -monitor none -semihosting-config enable=on,target=native \
      -kernel "$out/$name.elf" >"$out/$name.echo" 2>"$out/$name.stderr"; then
    echo "pass: $name: $(cat "$out/$name.echo"); bound $(cut -d' ' -f1 "$out/$name.elf.bound")," \
      "helpers $(awk '{print $3}' "$out/$name.elf.helpers" | paste -sd' ')"
  else
    echo "fail: $name: $(cat "$out/$name.echo" "$out/$name.stderr" | paste -sd' ' | head -c 400)"
    status=1
  fi
done
exit "$status"
