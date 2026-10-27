#!/usr/bin/env bash
# The startup code of tools/baremetal under QEMU's virt machine for AArch64, with the checks that
# reproduce the experiments of docs/native-bare-metal.md.  tests/baremetal/probe.c must print the
# words of probe.expected and exit with status 42, and its object may name no undefined symbol
# but lx_uart_dr.  With an unaligned 8-byte load before main it must do the same, since QEMU does
# not fault on such a load with the MMU off.  Without the enabling of floating point it must stop
# at vector 4 with the exception class 0x07 in ESR_EL1 and exit with status 255.  entry.c must
# print the exception level 1, DAIF 0x3c0, and SCTLR_EL1 0x00c50838 of entry.expected.  QEMU's
# device tree must place the PL011 at the address of lx_uart_dr in tools/baremetal/link.ld.  The
# reports' stack high-water marks, 16,048 and 48 bytes, are those of CompCert 3.18's code.  CCOMP
# and CCOMP_STDLIB are as for tools/baremetal/build.sh; NM, QEMU, and DTC name nm for AArch64
# objects, qemu-system-aarch64, and the device-tree compiler.
# Usage: tests/baremetal/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
here=$root/tests/baremetal
out=$root/build/baremetal
nm=${NM:-nm}
qemu=${QEMU:-qemu-system-aarch64}
dtc=${DTC:-dtc}
rm -rf "$out"
mkdir -p "$out"
status=0

fail() {
  echo "baremetal: $1" >&2
  status=1
}

# Runs the image $1 and leaves its UART output in $out/serial.txt and its exit status in $code.
run() {
  rm -f "$out/serial.txt"
  code=0
  timeout 120 "$qemu" -M virt -cpu cortex-a57 -m 1G -display none -monitor none \
    -serial "file:$out/serial.txt" -semihosting-config enable=on,target=native \
    -kernel "$1" </dev/null || code=$?
}

"$root/tools/baremetal/build.sh" "$here/probe.c" "$out/probe.elf"
undefined=$("$nm" -u "$out/probe.elf.program.o" | awk '{print $2}' | paste -sd' ')
if [ "$undefined" != "lx_uart_dr" ]; then
  fail "probe.c names undefined symbols other than lx_uart_dr: $undefined"
fi
run "$out/probe.elf"
if [ "$code" -ne 42 ] || ! diff "$here/probe.expected" <(grep -v '^R:' "$out/serial.txt") ||
    ! grep -qx 'R:exit 42 el 1 stack 16048' "$out/serial.txt"; then
  fail "probe.c gave status $code and $(paste -sd' ' "$out/serial.txt")"
fi

"$root/tools/baremetal/build.sh" "$here/probe.c" "$out/unaligned.elf" -DUNALIGNED_TEST
run "$out/unaligned.elf"
if [ "$code" -ne 42 ] || ! diff "$here/probe.expected" <(grep -v '^R:' "$out/serial.txt"); then
  fail "probe.c after an unaligned load gave status $code and $(paste -sd' ' "$out/serial.txt")"
fi

"$root/tools/baremetal/build.sh" "$here/probe.c" "$out/nofp.elf" -DNO_FPEN
run "$out/nofp.elf"
if [ "$code" -ne 255 ] || ! grep -q '^R:exception 4 esr 0x000000001fe00000 ' "$out/serial.txt"; then
  fail "probe.c without floating point gave status $code and $(paste -sd' ' "$out/serial.txt")"
fi

"$root/tools/baremetal/build.sh" "$here/entry.c" "$out/entry.elf"
run "$out/entry.elf"
if [ "$code" -ne 0 ] || ! diff "$here/entry.expected" <(grep -v '^R:' "$out/serial.txt") ||
    ! grep -qx 'R:exit 0 el 1 stack 48' "$out/serial.txt"; then
  fail "entry.c gave status $code and $(paste -sd' ' "$out/serial.txt")"
fi

"$qemu" -machine "virt,dumpdtb=$out/virt.dtb" -cpu cortex-a57 -m 1G -display none \
  -monitor none </dev/null
uart=$(sed -n 's/^ *lx_uart_dr = 0x0*\([0-9a-fA-F]*\);$/\1/p' "$root/tools/baremetal/link.ld")
"$dtc" -I dtb -O dts -o "$out/virt.dts" "$out/virt.dtb"
if ! grep -q "pl011@$uart {" "$out/virt.dts" ||
    ! grep -q "stdout-path = \"/pl011@$uart\";" "$out/virt.dts"; then
  fail "QEMU's device tree places no PL011 at 0x$uart, the address of lx_uart_dr"
fi

if [ "$status" -eq 0 ]; then
  echo "baremetal: probe, unaligned, nofp, entry, and the device tree agree with the experiments"
fi
exit $status
