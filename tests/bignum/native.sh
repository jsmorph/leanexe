#!/usr/bin/env bash
# Builds the C forms of the bignum library's three modules, runs them, and compares their output
# with the WebAssembly modules'.  Run after tests/bignum/run.sh, which writes the cases and the
# modules' results under build/bignum.
#
# The script builds the theorems of the C forms, Library.Numerics.Bignum.NativeRuntime,
# Library.Numerics.Bignum.Second.NativeRuntime, and Library.Numerics.Bignum.Third.NativeRuntime.
# For each module, EmitNative.lean writes the C text of the translation of compiled.module with
# lx_mem of nativeCap pages (bignum.c, bignum2.c, bignum3.c), clightgen reads it back, and
# EmitNative.lean compares that reading with the program of the theorems.  ccomp compiles the
# translation and the module's host program (tests/bignum/bignum.c, second/bignum2.c,
# third/bignum3.c), which places each argument in lx_mem through the module's alloc, calls the
# export, prints the result in the form of check.mjs's module.txt, and releases every block.  On
# every call the host's output must equal the WebAssembly module's: calls.txt for the first
# module, whose host reads the arguments as words, and cases.txt for the others.  CompCert's
# AArch64 programs run natively on an AArch64 host, and on another host under qemu-aarch64 with
# the AArch64 sysroot of QEMU_LD_PREFIX, /usr/aarch64-linux-gnu unless set.
#
# CCOMP, CLIGHTGEN, and CCOMP_STDLIB name the driver, clightgen, and run-time library of one
# AArch64 CompCert 3.18 tree with the change to Pallocframe of docs/trusted-base.md, as for
# tests/native/verified.sh.
# Usage: tests/bignum/native.sh
set -euo pipefail
if [ "$#" -ne 0 ]; then
  echo "usage: tests/bignum/native.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
out=build/bignum

tools/leanrun --timeout 3h lake build Library.Numerics.Bignum.NativeRuntime \
  Library.Numerics.Bignum.Second.NativeRuntime Library.Numerics.Bignum.Third.NativeRuntime
status=0
# Builds and runs the C form whose emitter and host are in the directory $1, whose C text is $2.c,
# and whose host reads $3 and must print $4.
form() {
  local dir=$1 name=$2 input=$3 want=$4 nat=$out/native/$2
  mkdir -p "$nat"
  tools/leanrun --timeout 30m lake env lean --run "$dir/EmitNative.lean" emit "$nat"
  (cd "$nat" && "$clightgen" "$name.c")
  tools/leanrun --timeout 30m lake env lean --run "$dir/EmitNative.lean" check "$nat"
  "$ccomp" -fno-common -c "$nat/$name.c" -o "$nat/$name.o"
  "$ccomp" -c "$dir/$name.c" -o "$nat/host.o"
  "$ccomp" "${stdlib[@]}" "$nat/$name.o" "$nat/host.o" -o "$nat/$name"
  local run=("$nat/$name")
  if [ "$(uname -m)" != aarch64 ]; then
    run=(qemu-aarch64 -L "${QEMU_LD_PREFIX:-/usr/aarch64-linux-gnu}" "$nat/$name")
  fi
  "${run[@]}" <"$input" >"$nat/calls.out"
  if cmp -s "$nat/calls.out" "$want"; then
    echo "$name: aarch64 Linux: the C form's output equals the WebAssembly module's on" \
      "$(wc -l <"$input") calls"
  else
    echo "fail: $name: the C form's output differs from the module's"
    status=1
  fi
}
form tests/bignum bignum "$out/calls.txt" "$out/module.txt"
form tests/bignum/second bignum2 "$out/second/cases.txt" "$out/second/module.txt"
form tests/bignum/third bignum3 "$out/third/cases.txt" "$out/third/module.txt"
exit "$status"
