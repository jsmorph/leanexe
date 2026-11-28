#!/usr/bin/env bash
# Tests the bignum library's three modules, Library.Numerics.Bignum.Compiled (bignum.wasm),
# Library.Numerics.Bignum.Second.Compiled (bignum2.wasm), and
# Library.Numerics.Bignum.Third.Compiled (bignum3.wasm), against Node's BigInt, and the module's
# results against the Lean functions and the specification evaluated in native Lean.
#
# The script builds the call theorems of the three modules and TestSupport.Bignum.Cases, whose
# #guard cases evaluate the divisions of Lean's convention, which no module exports.  It emits the
# modules into build/bignum with tools/Emit.lean and validates them with wasm-tools.
#   tests/bignum/check.mjs compares every export of bignum.wasm with Node's BigInt, checks that
#     the comparison rejects three mutated results and that the module releases every block it
#     allocates, and writes the cases, the module's results, and the calls of tests/bignum/native.sh.
#   tests/bignum/Native.lean evaluates the specification on those cases in native Lean.
#   tests/bignum/second/check.mjs compares the exports of bignum2.wasm with Node's BigInt and with
#     the first module's natMul, intMul, and intOfText, and tests/bignum/second/Native.lean
#     evaluates the second module's functions in native Lean beside the first module's and the
#     specification.
#   tests/bignum/third/check.mjs and tests/bignum/third/Native.lean do the same for bignum3.wasm
#     and the first module's divisions and printer.
# Each native Lean output must equal the module's results byte for byte.  Every Lean and Lake
# command runs under tools/leanrun with the caller's LEANRUN_THREADS and LEANRUN_MEMORY_HIGH.  The
# script needs Node and the wasm-tools of .wasm-tools-version.
# Usage: tests/bignum/run.sh
set -euo pipefail
if [ "$#" -ne 0 ]; then
  echo "usage: tests/bignum/run.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=build/bignum

tools/leanrun --timeout 3h lake build Library.Numerics.Bignum.Call \
  Library.Numerics.Bignum.Second.Call Library.Numerics.Bignum.Third.Call TestSupport.Bignum.Cases
mkdir -p "$out/second" "$out/third"
# Writes the module of the namespace $1 to $out/$2.wasm and validates it.
emit() {
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$1.Compiled" "$1.compiled.module" \
    "$out/$2.wasm"
  wasm-tools validate "$out/$2.wasm"
}
emit Library.Numerics.Bignum bignum
emit Library.Numerics.Bignum.Second bignum2
emit Library.Numerics.Bignum.Third bignum3

node tests/bignum/check.mjs "$out/bignum.wasm" "$out/cases.txt" "$out/module.txt" "$out/calls.txt"
tools/leanrun --timeout 1h lake env lean --run tests/bignum/Native.lean "$out/cases.txt" \
  "$out/lean.txt"
cmp "$out/lean.txt" "$out/module.txt"
echo "bignum: the module equals the specification in native Lean on every case"

node tests/bignum/second/check.mjs "$out/bignum2.wasm" "$out/bignum.wasm" "$out/second/cases.txt" \
  "$out/second/module.txt"
tools/leanrun --timeout 1h lake env lean --run tests/bignum/second/Native.lean \
  "$out/second/cases.txt" "$out/second/lean.txt"
cmp "$out/second/lean.txt" "$out/second/module.txt"
echo "bignum2: the module equals the Lean functions in native Lean on every case"

node tests/bignum/third/check.mjs "$out/bignum3.wasm" "$out/bignum.wasm" "$out/third/cases.txt" \
  "$out/third/module.txt"
# The first module's Algorithm D reads past the end of a dividend shorter than the divisor, which
# the Lean runtime reports on the standard error, with a backtrace unless LEAN_BACKTRACE=0; the
# reads give 0, as the specification of xs[i]! states.
LEAN_BACKTRACE=0 tools/leanrun --timeout 1h lake env lean --run tests/bignum/third/Native.lean \
  "$out/third/cases.txt" "$out/third/lean.txt" 2>"$out/third/lean.err"
cmp "$out/third/lean.txt" "$out/third/module.txt"
echo "bignum3: the module equals the Lean functions in native Lean on every case"
