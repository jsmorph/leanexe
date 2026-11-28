#!/usr/bin/env bash
# Builds the calculator's AArch64 bare-metal program, runs it under QEMU's virt machine on the
# messages of tests/bignum-calc/messages.mjs, and compares its output with Node's BigInt.
#
# The script builds Demos.BignumCalc.Bare, the theorem of the whole program.
# tests/bignum-calc/EmitNative.lean writes message.c, the translation of messageCompiled.module
# followed by lx_in, lx_out, and the main of inMain around calcWords, clightgen reads it back, and
# EmitNative.lean compares that reading with the program of calc_program.  tools/baremetal/build.sh
# compiles the program with the startup code and links it for QEMU's virt machine, failing unless
# its stack bound holds.  messages.mjs writes each message, NAME.in, and the bytes that the program
# must write, NAME.want, the line of Node's BigInt packed in words after their count.  QEMU's
# generic loader places NAME.in at lx_in, 0x70000000.  For each message the UART output must begin
# with NAME.want, the startup code's report of exit status 0 must follow, the exit status must be
# 0, and the stack's high-water mark must not exceed the bound of main.  A length above inMax must
# give no output and the status 64.
#
# CCOMP and CCOMP_STDLIB name the driver and run-time library of an AArch64 CompCert 3.18 tree with
# the change to Pallocframe of docs/trusted-base.md, and CLIGHTGEN its clightgen, as for
# tests/baremetal/programs.sh.  ACCEL selects QEMU's accelerator, tcg by default or kvm, as
# tests/baremetal/qemu.sh describes, and BARE_COUNT, when set, keeps the first BARE_COUNT messages.
# Usage: tests/bignum-calc/bare.sh
set -euo pipefail
if [ "$#" -ne 0 ]; then
  echo "usage: tests/bignum-calc/bare.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
clightgen=${CLIGHTGEN:-clightgen}
host=tests/bignum-calc
out=build/bignum-calc/bare

tools/leanrun --timeout 3h lake build Demos.BignumCalc.Bare
mkdir -p "$out"
tools/leanrun --timeout 30m lake env lean --run "$host/EmitNative.lean" emit "$out"
(cd "$out" && "$clightgen" message.c)
tools/leanrun --timeout 30m lake env lean --run "$host/EmitNative.lean" check "$out"

source tests/baremetal/qemu.sh
defines=()
if [ "${#bm_defines[@]}" -gt 0 ]; then
  defines=(-- "${bm_defines[@]}")
fi
STACK_DEPTHS=$out/message.depth tools/baremetal/build.sh "$out/message.elf" "$out/message.c" \
  "${defines[@]}"
bound=$(cut -d' ' -f1 "$out/message.elf.bound")
msgs=$out/messages
rm -rf "$msgs"
node "$host/messages.mjs" "$msgs" ${BARE_COUNT:-}
status=0
# Runs the program on the input file $1 and compares its output with the file $2 and its exit
# status with $3.
run() {
  local in=$1 want=$2 n mark
  bm_run virt "$in.serial" "$out/message.elf" -device "loader,file=$in,addr=0x70000000,force-raw=on"
  n=$(stat -c %s "$want")
  mark=$(tail -c +"$((n + 1))" "$in.serial" | sed -n 's/^R:exit .* stack \([0-9]*\)$/\1/p')
  if [ "$code" != "$3" ] || ! cmp -s -n "$n" "$want" "$in.serial" ||
      ! tail -c +"$((n + 1))" "$in.serial" | grep -q "^R:exit $3 "; then
    echo "fail: $(basename "$in"): status $code, output $(od -An -c "$in.serial" | head -c 300)"
    status=1
  elif [ "${mark:-0}" -gt "$bound" ]; then
    echo "fail: $(basename "$in"): the stack's high-water mark $mark exceeds the bound $bound"
    status=1
  fi
  marks="$marks ${mark:-0}"
}
m=0
marks=""
for in in "$msgs"/*.in; do
  run "$in" "${in%.in}.want" 0
  m=$((m + 1))
done
printf '\371\377\377\000\000\000\000\000' >"$msgs/over.msg"
: >"$msgs/empty.want"
run "$msgs/over.msg" "$msgs/empty.want" 64
if [ "$status" = 0 ]; then
  echo "aarch64 bare metal ($accel): the program's output equals Node's BigInt line on $m" \
    "messages, with the status 0 and a stack within the bound of $bound bytes, the largest mark" \
    "$(echo $marks | tr ' ' '\n' | sort -n | tail -1), and the length inMax + 1 gives the status 64"
fi
exit "$status"
