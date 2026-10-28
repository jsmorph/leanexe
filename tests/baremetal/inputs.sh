#!/usr/bin/env bash
# The programs with input under QEMU's virt machine for AArch64 (docs/native-bare-metal.md, B7).
# native-bare writes each program's C text, its translation followed by lx_in, lx_out, and the
# main that reads the input, and clightgen reads each C text back; native-bare check-in compares
# the whole program with the program of the theorem.  Each program is built with
# tools/baremetal/build.sh, whose stack bound must hold, and runs once per input file in its own
# QEMU process, whose stack's high-water mark must not exceed the larger of the bounds of main and
# of the report, with QEMU's generic loader placing the file at lx_in, 0x70000000: the length in
# eight bytes, the lowest first, then the message.  For sha256in, the UART output must be the
# message's SHA-256 digest as sha256sum computes it, followed by the startup code's report of exit
# status 0, which must be the program's exit status.  A length above 2^24 - 8 must give no output
# and the status 64.  The messages have the lengths 0, 3 (abc), 55, 56, 63, 64, 65, 1,000,
# 65,536, 1,048,576, and 2^24 - 8, the largest accepted, with random bytes beyond abc.  ACCEL
# selects the accelerator, as tests/baremetal/qemu.sh describes.  CCOMP, CCOMP_STDLIB, and
# CLIGHTGEN name CompCert 3.18's driver, run-time library, and clightgen for AArch64.
# Usage: tests/baremetal/inputs.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/baremetal/inputs
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
tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare emit-in "$out"
for c in "$out"/*.c; do
  (cd "$out" && "$clightgen" "$(basename "$c")")
done
tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare check-in "$out"
"$ccomp" "${stdlib[@]}" -S tools/baremetal/report.c -o "$out/report.s"
report=$(tools/baremetal/stack-bound.sh -r lx_report_exit /dev/null "$out/report.s" | cut -d' ' -f1)

# The eight bytes of the number $1, the lowest first.
le64() {
  local n=$1 i hex=""
  for i in 0 1 2 3 4 5 6 7; do
    hex+=$(printf '%02x' $(((n >> (8 * i)) & 255)))
  done
  printf '%s' "$hex" | xxd -r -p
}

# Writes the input file $1 for the message file $2.
input() {
  { le64 "$(stat -c %s "$2")"; cat "$2"; } >"$1"
}

name=sha256in
if ! STACK_DEPTHS=$out/$name.depth tools/baremetal/build.sh "$out/$name.elf" "$out/$name.c" -- \
    "${bm_defines[@]}" >"$out/$name.build" 2>&1; then
  echo "fail: $name: $(head -n 3 "$out/$name.build" | paste -sd' ')"
  exit 1
fi

status=0
# Runs the program on the input file $1 and compares its output with the file $2 and its exit
# status with $3.
run() {
  local in=$1 want=$2 code label
  label=$(basename "$in")
  TIMEOUT=1200 bm_run virt "$in.serial" "$out/$name.elf" \
    -device "loader,file=$in,addr=0x70000000,force-raw=on"
  local n bound mark
  n=$(stat -c %s "$want")
  bound=$(cut -d' ' -f1 "$out/$name.elf.bound")
  mark=$(tail -c +"$((n + 1))" "$in.serial" | sed -n 's/^R:exit .* stack \([0-9]*\)$/\1/p')
  if [ "$code" != "$3" ] || ! cmp -s -n "$n" "$want" "$in.serial" ||
      ! tail -c +"$((n + 1))" "$in.serial" | grep -q "^R:exit $3 "; then
    echo "fail: $name $label: status $code, output $(od -An -tx1 "$in.serial" | head -c 200)"
    status=1
  elif [ "${mark:-0}" -gt "$bound" ] && [ "${mark:-0}" -gt "$report" ]; then
    echo "fail: $name $label: the stack's high-water mark $mark exceeds the bounds $bound of main\
 and $report of the report"
    status=1
  else
    echo "pass: $name $label: $n bytes, $(tail -c +"$((n + 1))" "$in.serial" | tr -d '\n'),\
 bound $bound"
  fi
}

for len in 0 3 55 56 63 64 65 1000 65536 1048576 16777208; do
  msg=$out/msg$len
  if [ "$len" -eq 3 ]; then
    printf 'abc' >"$msg"
  else
    head -c "$len" /dev/urandom >"$msg"
  fi
  input "$out/in$len" "$msg"
  sha256sum "$msg" | cut -c1-64 | xxd -r -p >"$msg.digest"
  run "$out/in$len" "$msg.digest" 0
done

: >"$out/empty"
le64 16777209 >"$out/inlong"
run "$out/inlong" "$out/empty" 64
le64 -1 >"$out/inmax"
run "$out/inmax" "$out/empty" 64
exit "$status"
