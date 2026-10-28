#!/usr/bin/env bash
# The programs with a generated main under QEMU's virt machine for AArch64
# (docs/native-bare-metal.md, test 2).  native-bare writes each program's C text, its translation
# followed by lx_out and main, and the bytes that main must write, which are those of the Lean
# function's result and of Talos's.  clightgen reads each C text back, and native-bare check
# compares the whole program, CompCert's declarations and main included, with the program of the
# theorem.  Each program is built with tools/baremetal/build.sh and run in its own QEMU process:
# the build fails unless tools/baremetal/stack-bound.sh bounds the stack of main within the
# stack size, and the stack's high-water mark must not exceed the larger of the bounds of main
# and of the report after it.  Its UART output must begin with the expected bytes, followed by
# the startup code's report of the expected exit status, which must be the program's exit status:
# 0 after the result's bytes, or the code of unreachable, with no byte before the report, for a
# run that Talos ends with that trap.  ACCEL selects the accelerator, as tests/baremetal/qemu.sh
# describes.  CCOMP, CCOMP_STDLIB, and CLIGHTGEN name CompCert 3.18's driver, run-time library,
# and clightgen for AArch64.
# Usage: tests/baremetal/programs.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/baremetal/programs
clightgen=${CLIGHTGEN:-clightgen}
ccomp=${CCOMP:-ccomp}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
source tests/baremetal/qemu.sh
rm -rf "$out"
mkdir -p "$out"

tools/leanrun --timeout 60m lake --log-level error build native-bare
tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare emit "$out"
for c in "$out"/*.c; do
  (cd "$out" && "$clightgen" "$(basename "$c")")
done
tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare check "$out"
"$ccomp" "${stdlib[@]}" -S tools/baremetal/report.c -o "$out/report.s"
report=$(tools/baremetal/stack-bound.sh -r lx_report_exit /dev/null "$out/report.s" | cut -d' ' -f1)

status=0
for c in "$out"/*.c; do
  name=$(basename "${c%.c}")
  if ! STACK_DEPTHS=$out/$name.depth tools/baremetal/build.sh "$out/$name.elf" "$c" -- \
      "${bm_defines[@]}" >"$out/$name.build" 2>&1; then
    echo "fail: $name: $(head -n 3 "$out/$name.build" | paste -sd' ')"
    status=1
    continue
  fi
  TIMEOUT=600 bm_run virt "$out/$name.serial" "$out/$name.elf"
  n=$(stat -c %s "$out/$name.expected")
  want=$(cat "$out/$name.status")
  bound=$(cut -d' ' -f1 "$out/$name.elf.bound")
  mark=$(tail -c +"$((n + 1))" "$out/$name.serial" | sed -n 's/^R:exit .* stack \([0-9]*\)$/\1/p')
  if [ "$code" != "$want" ] || ! cmp -s -n "$n" "$out/$name.expected" "$out/$name.serial" ||
      ! tail -c +"$((n + 1))" "$out/$name.serial" | grep -q "^R:exit $want "; then
    echo "fail: $name: status $code, output $(od -An -tx1 "$out/$name.serial" | head -c 200)"
    status=1
  elif [ "${mark:-0}" -gt "$bound" ] && [ "${mark:-0}" -gt "$report" ]; then
    echo "fail: $name: the stack's high-water mark $mark exceeds the bounds $bound of main and\
 $report of the report"
    status=1
  else
    echo "pass: $name: $n bytes, $(tail -c +"$((n + 1))" "$out/$name.serial" | tr -d '\n'),\
 bound $bound"
  fi
done
exit "$status"
