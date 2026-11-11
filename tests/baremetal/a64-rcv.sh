#!/usr/bin/env bash
# The Oakland tabulator's AArch64 Image of tests/TestSupport/A64/Rcv.lean, which reads a canonical
# file over the UART, on the canonical files of each DIR under QEMU's virt machine.  a64-rcv emit
# writes the Image, rcv.img, into OUT, build/baremetal/a64-rcv unless set, and the script checks
# QEMU's loading of it with tests/baremetal/a64-loadcheck.sh.  With --check, Lean elaborates
# tests/TestSupport/A64/ImageFilesRcv.lean in OUT with a MemoryHigh of MEM, 48G unless set, so that
# the kernel checks that rcv.img holds the bytes that the generator gives and proves the Image's
# theorems, and the script requires four theorems with no axiom beyond propext, Classical.choice,
# and Quot.sound.  tests/baremetal/a64_rcv.py then runs the Image on each file, with the
# accelerator that ACCEL selects, as tests/baremetal/qemu.sh describes, and each run within
# TIMEOUT seconds, 600 unless set, and requires the report of build/rcv/native/rcv-tabulate-c, the
# C translation, which must equal that of build/rcv/process.wasm, the WASI process, in
# build/tools/leanexe-wasmtime-host, and the status 0.  The commands of "Running the tabulator" in
# Demos/Rcv/README.md build the two references.  The script prints the times of a64_rcv.py and
# writes the times of each file to OUT/times-ACCEL.tsv.
# Usage: tests/baremetal/a64-rcv.sh [--check] DIR...
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
check=0
if [ "${1:-}" = --check ]; then
  check=1
  shift
fi
[ "$#" -ge 1 ] || { echo "usage: tests/baremetal/a64-rcv.sh [--check] DIR..." >&2; exit 2; }
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-rcv}")
accel=${ACCEL:-tcg}
mkdir -p "$out"
targets=(a64-rcv)
if [ "$check" = 1 ]; then
  targets+=(TestSupport.A64.RcvRuns LeanExe.A64.File)
fi
tools/leanrun --timeout 120m --memory-high 16G lake --log-level error build "${targets[@]}"
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-rcv emit "$out"
tests/baremetal/a64-loadcheck.sh "$out/rcv.img"
status=0
if [ "$check" = 1 ]; then
  if tools/leanrun --timeout 120m --memory-high "${MEM:-48G}" lake env \
      sh -c 'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/A64/ImageFilesRcv.lean" \
      >"$out/ImageFilesRcv.check" 2>&1 &&
      [ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' \
        "$out/ImageFilesRcv.check")" = 4 ]; then
    echo "pass: the kernel's check of ImageFilesRcv.lean"
  else
    echo "fail: the kernel's check of ImageFilesRcv.lean: $(head -c 600 "$out/ImageFilesRcv.check")"
    status=1
  fi
fi
uv run tests/baremetal/a64_rcv.py --image "$out/rcv.img" --accel "$accel" \
  --timeout "${TIMEOUT:-600}" --work "$out/work-$accel" --times "$out/times-$accel.tsv" \
  --native build/rcv/native/rcv-tabulate-c --host build/tools/leanexe-wasmtime-host \
  --process build/rcv/process.wasm "$@" || status=1
exit "$status"
