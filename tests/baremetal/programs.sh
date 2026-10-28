#!/usr/bin/env bash
# The programs with a generated main under QEMU's virt machine for AArch64
# (docs/native-bare-metal.md, test 2).  native-bare writes each program's C text, its translation
# followed by lx_out and main, and the bytes that main must write, which are those of the Lean
# function's result and of Talos's.  clightgen reads each C text back, and native-bare check
# compares the whole program, CompCert's declarations and main included, with the program of the
# theorem.  Each program is built with tools/baremetal/build.sh and run in its own QEMU process:
# its UART output must begin with the expected bytes, followed by the startup code's report of
# the expected exit status, with which QEMU must exit: 0 after the result's bytes, or the code of
# unreachable, with no byte before the report, for a run that Talos ends with that trap.  CCOMP,
# CCOMP_STDLIB, and CLIGHTGEN name CompCert 3.18's driver, run-time library, and clightgen for
# AArch64, and QEMU names qemu-system-aarch64.
# Usage: tests/baremetal/programs.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/baremetal/programs
clightgen=${CLIGHTGEN:-clightgen}
qemu=${QEMU:-qemu-system-aarch64}
rm -rf "$out"
mkdir -p "$out"

tools/leanrun --timeout 60m lake --log-level error build native-bare
tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare emit "$out"
for c in "$out"/*.c; do
  (cd "$out" && "$clightgen" "$(basename "$c")")
done
tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare check "$out"

status=0
for c in "$out"/*.c; do
  name=$(basename "${c%.c}")
  if ! tools/baremetal/build.sh "$out/$name.elf" "$c" >"$out/$name.build" 2>&1; then
    echo "fail: $name: $(head -n 3 "$out/$name.build" | paste -sd' ')"
    status=1
    continue
  fi
  code=0
  timeout 600 "$qemu" -M virt -cpu cortex-a57 -m 1G -display none -monitor none \
    -serial "file:$out/$name.serial" -semihosting-config enable=on,target=native \
    -kernel "$out/$name.elf" </dev/null || code=$?
  n=$(stat -c %s "$out/$name.expected")
  want=$(cat "$out/$name.status")
  if [ "$code" -ne "$want" ] || ! cmp -s -n "$n" "$out/$name.expected" "$out/$name.serial" ||
      ! tail -c +"$((n + 1))" "$out/$name.serial" | grep -q "^R:exit $want "; then
    echo "fail: $name: status $code, output $(od -An -tx1 "$out/$name.serial" | head -c 200)"
    status=1
  else
    echo "pass: $name: $n bytes, $(tail -c +"$((n + 1))" "$out/$name.serial" | tr -d '\n')"
  fi
done
exit "$status"
