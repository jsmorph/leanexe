#!/usr/bin/env bash
# The co-simulation of the AArch64 model of LeanExe/A64/Machine.lean against QEMU's virt machine,
# under TCG or under KVM on the host's processor (tests/TestSupport/A64/Cosim.lean).  It builds
# a64-cosim, writes the harness of PER_FORM cases of each of the model's forms from the seed SEED,
# assembles it, links it with tests/baremetal/a64cosim.c and the startup code through
# tools/baremetal/build.sh, runs the image with bm_run of tests/baremetal/qemu.sh, and checks every
# case line of its UART output against the model with a64-cosim check.  The run must end with
# status 0, and every case must agree.  ACCEL selects the accelerator, as qemu.sh describes, and
# CCOMP and CCOMP_STDLIB name CompCert 3.18's driver and run-time library for AArch64.  The
# products lie in OUT, build/baremetal/a64-cosim unless set.  The image is built with DEFAULT_NAN,
# with which the startup code sets FPCR.DN, as the back end's images are.
# Usage: tests/baremetal/a64-cosim.sh SEED PER_FORM
set -euo pipefail
[ "$#" -eq 2 ] || { echo "usage: tests/baremetal/a64-cosim.sh SEED PER_FORM" >&2; exit 2; }
seed=$1
per=$2
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-cosim}")
ccomp=${CCOMP:-ccomp}
source tests/baremetal/qemu.sh
mkdir -p "$out"
tools/leanrun --timeout 30m lake --log-level error build a64-cosim
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-cosim gen "$seed" "$per" "$out/cases.s"
"$ccomp" -c "$out/cases.s" -o "$out/cases.o"
tools/baremetal/build.sh "$out/cosim.elf" tests/baremetal/a64cosim.c "$out/cases.o" -- \
  "${bm_defines[@]}" -DDEFAULT_NAN >"$out/cosim.build" 2>&1 ||
  { echo "fail: the image did not build: $(head -c 400 "$out/cosim.build")"; exit 1; }
bm_run virt "$out/cosim.serial" "$out/cosim.elf"
if [ "$code" != 0 ]; then
  echo "fail: the run ended with status $code: $(tail -c 300 "$out/cosim.serial")"
  exit 1
fi
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-cosim check "$out/cosim.serial"
