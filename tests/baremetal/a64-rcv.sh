#!/usr/bin/env bash
# A tabulator's AArch64 Image, which reads a canonical file over the UART, on the canonical files
# of each DIR under QEMU's virt machine.  MODULE selects the tabulator: oakland, the default, the
# Image rcv.img of tests/TestSupport/A64/Rcv.lean, or maine, the Image maine.img of
# tests/TestSupport/A64/RcvMaine.lean.  a64-rcv emit writes both Images into OUT,
# build/baremetal/a64-rcv unless set, and the script checks QEMU's loading of the selected one with
# tests/baremetal/a64-loadcheck.sh.  With --check, Lean elaborates the Image's theorems,
# tests/TestSupport/A64/ImageFilesRcv.lean or ImageFilesRcvMaine.lean, in OUT with a MemoryHigh of
# MEM, 48G unless set, so that the kernel checks that the Image file holds the bytes that the
# generator gives and proves the Image's theorems, and the script requires four theorems with no
# axiom beyond propext, Classical.choice, and Quot.sound.  tests/baremetal/a64_rcv.py then runs
# the Image on each file, with the accelerator that ACCEL selects, as tests/baremetal/qemu.sh
# describes, and each run within TIMEOUT seconds, 600 unless set, and requires the report of the
# module's C translation, build/rcv/native/rcv-tabulate-c or build/rcv/maine/native/rcv-maine-c,
# which must equal that of its WASI process, build/rcv/process.wasm or build/rcv/maine/process.wasm,
# in build/tools/leanexe-wasmtime-host, and the status 0.  The commands of "Running the tabulator"
# in Demos/Rcv/README.md and of "Running the module" in Demos/Rcv/Maine/README.md build the
# references.  The script prints the times of a64_rcv.py and writes the times of each file to
# OUT/times-MODULE-ACCEL.tsv.
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
module=${MODULE:-oakland}
case "$module" in
  oakland)
    image=rcv.img
    theorems=ImageFilesRcv
    runs=TestSupport.A64.RcvRuns
    native=build/rcv/native/rcv-tabulate-c
    process=build/rcv/process.wasm
    ;;
  maine)
    image=maine.img
    theorems=ImageFilesRcvMaine
    runs=TestSupport.A64.RcvMaineRuns
    native=build/rcv/maine/native/rcv-maine-c
    process=build/rcv/maine/process.wasm
    ;;
  *)
    echo "MODULE must be oakland or maine, not $module" >&2
    exit 2
    ;;
esac
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-rcv}")
accel=${ACCEL:-tcg}
mkdir -p "$out"
targets=(a64-rcv)
if [ "$check" = 1 ]; then
  targets+=("$runs" LeanExe.A64.File)
fi
tools/leanrun --timeout 120m --memory-high 16G lake --log-level error build "${targets[@]}"
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-rcv emit "$out"
tests/baremetal/a64-loadcheck.sh "$out/$image"
status=0
if [ "$check" = 1 ]; then
  if tools/leanrun --timeout 120m --memory-high "${MEM:-48G}" lake env \
      sh -c 'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/A64/$theorems.lean" \
      >"$out/$theorems.check" 2>&1 &&
      [ "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]$' \
        "$out/$theorems.check")" = 4 ]; then
    echo "pass: the kernel's check of $theorems.lean"
  else
    echo "fail: the kernel's check of $theorems.lean: $(head -c 600 "$out/$theorems.check")"
    status=1
  fi
fi
uv run tests/baremetal/a64_rcv.py --image "$out/$image" --accel "$accel" \
  --timeout "${TIMEOUT:-600}" --work "$out/work-$module-$accel" \
  --times "$out/times-$module-$accel.tsv" --native "$native" \
  --host build/tools/leanexe-wasmtime-host --process "$process" "$@" || status=1
exit "$status"
