#!/usr/bin/env bash
# The co-simulation of the Cortex-M7 model of LeanExe/M7/Machine.lean against QEMU's mps2-an500,
# an emulated Cortex-M7 (tests/TestSupport/M7/Cosim.lean).  It builds m7-cosim, writes the harness
# of PER_FORM cases of each of the model's forms from the seed SEED, assembles it with CompCert's
# driver, links it with tests/baremetal/m7cosim.c and the startup code of tools/baremetal/armv7m
# for the board mps2-an500 through tools/baremetal/armv7m/build.sh, runs the image under QEMU, and
# checks every case line of its UART output against the model with m7-cosim check.  The startup
# code enables the floating-point unit, whose registers the harness uses to save the state after
# each case.  The run must end with status 0, through semihosting, and every case must agree.
# CCOMP and CCOMP_STDLIB name CompCert 3.18's driver configured armv7m-eabihf and its run-time
# library, as for build.sh, QEMU names qemu-system-arm, and TIMEOUT, 120 unless set, bounds the run
# in seconds.  The products lie in OUT, build/baremetal/m7-cosim unless set.
# Usage: tests/baremetal/m7-cosim.sh SEED PER_FORM
set -euo pipefail
[ "$#" -eq 2 ] || { echo "usage: tests/baremetal/m7-cosim.sh SEED PER_FORM" >&2; exit 2; }
seed=$1
per=$2
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/m7-cosim}")
ccomp=${CCOMP:-ccomp}
qemu=${QEMU:-qemu-system-arm}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
mkdir -p "$out"
tools/leanrun --timeout 30m lake --log-level error build m7-cosim
tools/leanrun --timeout 30m lake env .lake/build/bin/m7-cosim gen "$seed" "$per" "$out/cases.s"
"$ccomp" "${stdlib[@]}" -c "$out/cases.s" -o "$out/cases.o"
BOARD=mps2-an500 tools/baremetal/armv7m/build.sh "$out/cosim.elf" tests/baremetal/m7cosim.c \
  "$out/cases.o" >"$out/cosim.build" 2>&1 ||
  { echo "fail: the image did not build: $(head -c 400 "$out/cosim.build")"; exit 1; }
rm -f "$out/cosim.serial"
code=0
timeout "${TIMEOUT:-120}" "$qemu" -M mps2-an500 -display none -monitor none \
  -serial "file:$out/cosim.serial" -semihosting-config enable=on,target=native \
  -kernel "$out/cosim.elf" </dev/null || code=$?
if [ "$code" != 0 ]; then
  echo "fail: the run ended with status $code: $(tail -c 300 "$out/cosim.serial")"
  exit 1
fi
tools/leanrun --timeout 30m lake env .lake/build/bin/m7-cosim check "$out/cosim.serial"
