#!/usr/bin/env bash
# The startup code of tools/baremetal under QEMU's virt machine for AArch64, with the checks that
# reproduce the experiments of docs/native-bare-metal.md, under the accelerator that ACCEL
# selects as tests/baremetal/qemu.sh describes.  tests/baremetal/probe.c must print the words of
# probe.expected and exit with status 42, and its object may name no undefined symbol but
# lx_out.  With an unaligned 8-byte load before main it must do the same, since the startup code
# maps RAM as Normal memory with SCTLR_EL1.A clear.  With a store to the word below the stack it
# must stop at vector 4 with a level 3 translation fault on a write in ESR_EL1 and that word's
# address in FAR_EL1, and exit with status 255.  Without the enabling of floating point it must
# stop at vector 4 with the exception class 0x07 in ESR_EL1 and exit with status 255.  entry.c
# must print the exception level 1, DAIF 0x3c0, and, under TCG, SCTLR_EL1 0x00c50838 of
# entry.expected, since under KVM the value at entry is the one that KVM's reset gives.  Under
# TCG, on the machines with the virtualization extensions and with the security extensions,
# which enter the image at EL2 and EL3, it must report the level and exit with status 254.
# QEMU's device tree must place the PL011 at the address of lx_out in tools/baremetal/link.ld
# and the RAM at __ram_start with the size of __ram_end - __ram_start, and must name PSCI with
# the method hvc, which PSCI_EXIT uses.  The reports' stack high-water marks, 16,048 bytes for
# probe.c and 32 for entry.c, are those of main and its callees as CompCert 3.18 compiles them.
# CCOMP and CCOMP_STDLIB are as for tools/baremetal/build.sh, and NM and DTC name nm for AArch64
# objects and the device-tree compiler.
# Usage: tests/baremetal/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
here=$root/tests/baremetal
out=$root/build/baremetal
nm=${NM:-nm}
dtc=${DTC:-dtc}
source "$here/qemu.sh"
rm -rf "$out"
mkdir -p "$out"
status=0

fail() {
  echo "baremetal: $1" >&2
  status=1
}

# Builds the image $1 from probe.c or entry.c, $2, with the startup code's defines after $2.
build() {
  local image=$1 source=$2
  shift 2
  "$root/tools/baremetal/build.sh" "$out/$image" "$here/$source" -- "${bm_defines[@]}" "$@"
}

# Runs the image $1 on the machine $2, virt by default, and leaves its UART output in
# $out/serial.txt and its exit status in $code.
run() {
  bm_run "${2:-virt}" "$out/serial.txt" "$1"
}

build probe.elf probe.c
undefined=$("$nm" -u "$out/probe.elf.probe.o" | awk '{print $2}' | paste -sd' ')
if [ "$undefined" != "lx_out" ]; then
  fail "probe.c names undefined symbols other than lx_out: $undefined"
fi
run "$out/probe.elf"
if [ "$code" != 42 ] || ! diff "$here/probe.expected" <(grep -v '^R:' "$out/serial.txt") ||
    ! grep -qx 'R:exit 42 el 1 stack 16048' "$out/serial.txt"; then
  fail "probe.c gave status $code and $(paste -sd' ' "$out/serial.txt")"
fi

build unaligned.elf probe.c -DUNALIGNED_TEST
run "$out/unaligned.elf"
if [ "$code" != 42 ] || ! diff "$here/probe.expected" <(grep -v '^R:' "$out/serial.txt"); then
  fail "probe.c after an unaligned load gave status $code and $(paste -sd' ' "$out/serial.txt")"
fi

build guard.elf probe.c -DGUARD_TEST
bottom=$("$nm" "$out/guard.elf" | awk '$3 == "__stack_bottom" { print $1 }')
far=$(printf '0x%016x' $((0x$bottom - 8)))
run "$out/guard.elf"
if [ "$code" != 255 ] ||
    ! grep -q "^R:exception 4 esr 0x0000000096000047 elr 0x[0-9a-f]* far $far\$" \
      "$out/serial.txt"; then
  fail "probe.c after a store below the stack gave status $code and\
 $(paste -sd' ' "$out/serial.txt")"
fi

build nofp.elf probe.c -DNO_FPEN
run "$out/nofp.elf"
if [ "$code" != 255 ] || ! grep -q '^R:exception 4 esr 0x000000001fe00000 ' "$out/serial.txt"; then
  fail "probe.c without floating point gave status $code and $(paste -sd' ' "$out/serial.txt")"
fi

build entry.elf entry.c
run "$out/entry.elf"
lines=3
if [ "$accel" = kvm ]; then
  lines=2
fi
if [ "$code" != 0 ] ||
    ! diff <(head -n "$lines" "$here/entry.expected") \
      <(grep -v '^R:' "$out/serial.txt" | head -n "$lines") ||
    ! grep -qx 'R:exit 0 el 1 stack 32' "$out/serial.txt"; then
  fail "entry.c gave status $code and $(paste -sd' ' "$out/serial.txt")"
fi
if [ "$accel" = tcg ]; then
  for level in 2 3; do
    if [ "$level" -eq 2 ]; then
      machine=virt,virtualization=on
    else
      machine=virt,secure=on
    fi
    run "$out/entry.elf" "$machine"
    if [ "$code" != 254 ] || ! grep -qx "R:level $level" "$out/serial.txt"; then
      fail "entry.c at EL$level gave status $code and $(paste -sd' ' "$out/serial.txt")"
    fi
  done
fi

"$qemu" -machine "virt,dumpdtb=$out/virt.dtb" "${bm_cpu[@]}" -m 1G -display none \
  -monitor none </dev/null
ld=$root/tools/baremetal/link.ld
uart=$(sed -n 's/^ *lx_out = 0x0*\([0-9a-fA-F]*\);$/\1/p' "$ld")
ram=$(sed -n 's/^ *__ram_start = 0x0*\([0-9a-fA-F]*\);$/\1/p' "$ld")
ramend=$(sed -n 's/^ *__ram_end = \(0x[0-9a-fA-F]*\);$/\1/p' "$ld")
size=$(printf '0x%x' $((ramend - 0x$ram)))
"$dtc" -I dtb -O dts -o "$out/virt.dts" "$out/virt.dtb"
if ! grep -q "pl011@$uart {" "$out/virt.dts" ||
    ! grep -q "stdout-path = \"/pl011@$uart\";" "$out/virt.dts"; then
  fail "QEMU's device tree places no PL011 at 0x$uart, the address of lx_out"
fi
# Succeeds when the node that begins with the line containing $1 has a line containing $2.
has() {
  awk -v node="$1" -v line="$2" '
    index($0, node) { inside = 1 }
    inside && index($0, line) { found = 1 }
    inside && /};/ { inside = 0 }
    END { exit !found }' "$out/virt.dts"
}
if ! has "memory@$ram {" "reg = <0x00 0x$ram 0x00 $size>;"; then
  fail "QEMU's device tree gives no RAM of $size bytes at 0x$ram"
fi
if ! has "psci {" 'method = "hvc";'; then
  fail "QEMU's device tree names no PSCI with the method hvc"
fi

if [ "$status" -eq 0 ]; then
  if [ "$accel" = tcg ]; then
    echo "baremetal: probe, unaligned, guard, nofp, entry at EL1, EL2, and EL3, and the device" \
      "tree pass under TCG"
  else
    echo "baremetal: probe, unaligned, guard, nofp, entry at EL1, and the device tree pass under" \
      "KVM"
  fi
fi
exit $status
