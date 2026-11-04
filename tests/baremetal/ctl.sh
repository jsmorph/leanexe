#!/usr/bin/env bash
# The controller programs under QEMU's virt machine for AArch64.  native-bare writes each
# program's C text, its translation followed by lx_in, lx_out, and the main that runs the step
# forever, the names of the functions that take the call depth, the eight bytes of lx_in, and
# the bytes of the first windows, which the step's Lean function gives.  clightgen reads each C
# text back, and native-bare check-ctl compares the whole program with the program of the
# theorem.  Each window of main reads lx_in[0] to lx_in[7] by volatile byte loads as a word, the
# lowest byte first, calls the step on the state and the word, and writes the eight bytes of the
# new state to lx_out, the lowest first.  Each program is built with tools/baremetal/build.sh,
# whose stack bound must hold, and runs in its own QEMU process, with QEMU's generic loader
# placing NAME.in at lx_in, 0x70000000.  main never returns, so the startup code's report, with
# the stack's high-water mark, never comes.  Once the UART output reaches the size of
# NAME.expected, eight bytes per window, QEMU stops and must exit with status 0, and the output
# must equal NAME.expected.  The module NAME.wasm then runs the step in Wasmtime, one call per
# window to the export named in NAME.export, from the state in NAME.state and the word of
# NAME.in, and the eight bytes of each new state, the lowest first, must also equal
# NAME.expected.  ACCEL selects the accelerator, as tests/baremetal/qemu.sh describes, and
# TIMEOUT, 120 unless set, bounds each run in seconds.  CCOMP, CCOMP_STDLIB, and CLIGHTGEN name
# CompCert 3.18's driver, run-time library, and clightgen for AArch64, and the script builds
# build/tools/leanexe-wasmtime-host when it is missing.
# Usage: tests/baremetal/ctl.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/baremetal/ctl
clightgen=${CLIGHTGEN:-clightgen}
host=$root/build/tools/leanexe-wasmtime-host
source tests/baremetal/qemu.sh
rm -rf "$out"
mkdir -p "$out"

[ -x "$host" ] || tools/build-wasmtime-host.sh
tools/leanrun --timeout 60m lake --log-level error build native-bare
tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare emit-ctl "$out"
for c in "$out"/*.c; do
  (cd "$out" && "$clightgen" "$(basename "$c")")
done
tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare check-ctl "$out"

# The eight bytes of the number $1, the lowest first.
le64() {
  local n=$1 i hex=""
  for i in 0 1 2 3 4 5 6 7; do
    hex+=$(printf '%02x' $(((n >> (8 * i)) & 255)))
  done
  printf '%s' "$hex" | xxd -r -p
}

status=0
for c in "$out"/*.c; do
  name=$(basename "${c%.c}")
  if ! STACK_DEPTHS=$out/$name.depth tools/baremetal/build.sh "$out/$name.elf" "$c" -- \
      "${bm_defines[@]}" >"$out/$name.build" 2>&1; then
    echo "fail: $name: $(head -n 3 "$out/$name.build" | paste -sd' ')"
    status=1
    continue
  fi
  n=$(stat -c %s "$out/$name.expected")
  bm_stream virt "$out/$name.serial" "$out/$name.elf" "$n" \
    -device "loader,file=$out/$name.in,addr=0x70000000,force-raw=on"
  bound=$(cut -d' ' -f1 "$out/$name.elf.bound")
  if [ "$code" != 0 ] || ! cmp -s "$out/$name.expected" "$out/$name.serial"; then
    echo "fail: $name: status $code, output $(od -An -tx1 "$out/$name.serial" | head -c 200)"
    status=1
  else
    echo "pass: $name: $((n / 8)) windows, $n bytes, bound $bound"
  fi
  x=$(od -An -tu8 -N8 "$out/$name.in" | tr -d ' ')
  s=$(cat "$out/$name.state")
  : >"$out/$name.wasmtime"
  for ((i = 0; i < n / 8; i++)); do
    s=$("$host" call "$out/$name.wasm" "$(cat "$out/$name.export")" i64 "i64:$s" "i64:$x")
    le64 "$s" >>"$out/$name.wasmtime"
  done
  if cmp -s "$out/$name.expected" "$out/$name.wasmtime"; then
    echo "pass: $name: Wasmtime, $((n / 8)) windows, module of $(stat -c %s "$out/$name.wasm") bytes"
  else
    echo "fail: $name: Wasmtime output $(od -An -tx1 "$out/$name.wasmtime" | head -c 200)"
    status=1
  fi
done
exit "$status"
