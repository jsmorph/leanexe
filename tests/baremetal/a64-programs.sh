#!/usr/bin/env bash
# The bare-metal programs of the AArch64 back end (LeanExe/A64/Gen.lean) under QEMU's virt
# machine.  a64-programs emit generates each program, checks it in the model, and writes the
# bytes of its instructions, the assembly of the section .text.a64 that includes them after the
# exit word, and the bytes it must write.  Each program is assembled, linked with the startup code
# through tools/baremetal/build.sh, and run with bm_run of tests/baremetal/qemu.sh.  The image
# must place main at 0x40100004, the address for which a64-programs generated the code, and its
# section .text, which the link script starts with .text.a64 at 0x40100000, must hold the
# instructions' bytes from main.  The UART output must
# begin with the expected bytes, followed by the startup code's report of exit status 0, which
# must be the program's exit status.  ACCEL selects the accelerator, as qemu.sh
# describes, and CCOMP and CCOMP_STDLIB name CompCert 3.18's driver and run-time library for
# AArch64, which assemble the programs and the startup code, and NM and OBJCOPY name nm and
# objcopy for AArch64 objects.  The products lie in OUT,
# build/baremetal/a64-programs unless set.
# Usage: tests/baremetal/a64-programs.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-programs}")
ccomp=${CCOMP:-ccomp}
nm=${NM:-nm}
objcopy=${OBJCOPY:-objcopy}
source tests/baremetal/qemu.sh
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build a64-programs
status=0
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-programs emit "$out" || status=1
for s in "$out"/*.s; do
  name=$(basename "${s%.s}")
  if ! "$ccomp" -c "$s" -o "$out/$name.o" >"$out/$name.build" 2>&1 ||
      ! tools/baremetal/build.sh "$out/$name.elf" "$out/$name.o" -- "${bm_defines[@]}" \
        >>"$out/$name.build" 2>&1; then
    echo "fail: $name: $(head -c 300 "$out/$name.build")"
    status=1
    continue
  fi
  if [ "$("$nm" "$out/$name.elf" | awk '$3 == "main" { print $1 }')" != 0000000040100004 ] ||
      ! "$objcopy" -O binary --only-section=.text "$out/$name.elf" "$out/$name.text" ||
      ! cmp -s <(tail -c +5 "$out/$name.text" | head -c "$(stat -c %s "$out/$name.bin")") \
        "$out/$name.bin"; then
    echo "fail: $name: the image does not hold the program's bytes from main at 0x40100004"
    status=1
    continue
  fi
  bm_run virt "$out/$name.serial" "$out/$name.elf"
  n=$(stat -c %s "$out/$name.expected")
  if [ "$code" != 0 ] || ! cmp -s -n "$n" "$out/$name.expected" "$out/$name.serial" ||
      ! tail -c +"$((n + 1))" "$out/$name.serial" | grep -q "^R:exit 0 "; then
    echo "fail: $name: status $code, output $(od -An -tx1 "$out/$name.serial" | head -c 200)"
    status=1
  else
    echo "pass: $name: $n bytes, $(tail -c +"$((n + 1))" "$out/$name.serial" | tr -d '\n')"
  fi
done
exit "$status"
