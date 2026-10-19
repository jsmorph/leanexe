#!/usr/bin/env bash
# Writes the modules of the verified compiler's examples, validates them with wasm-tools, and
# compares their checked cases between the Wasmtime host and native Lean.
# A case with a sixth field also checks the allocation counters: the blocks allocated less those
# released must equal the field, the result's arrays and the host's arrays at borrowed parameters.
# A seventh field bounds the number of allocations, the host's included.  A case whose expected
# result is
# `trap` must trap at `unreachable`.  After writing the modules, it builds each function's theorem
# module and checks its file theorem module, whose theorems state that the written file holds the
# module of the function's byte theorem, and it fails unless both file theorems report only the
# axioms propext, Classical.choice, and Quot.sound.  Last, the Verified/Examples/*Accuracy.lean
# checks compare the transcendental functions with references computed with Lean's integers, each
# within the bound its docstring states, and Verified/Examples/FourierAccuracy.lean checks that
# Fourier.dft, inverse, and powerSpectrum behave as their mathematical counterparts.
# Run `tools/leanrun --memory-high 10G --timeout 12h lake build Verified` first.
# Usage: tests/verified/run.sh [--cases MODULE]
set -euo pipefail
export PATH="$PATH:$HOME/.cargo/bin"
case_module=""
if [ "$#" -ne 0 ]; then
  if [ "$#" -ne 2 ] || [ "$1" != "--cases" ] || [ -z "$2" ]; then
    echo "usage: tests/verified/run.sh [--cases MODULE]" >&2
    exit 2
  fi
  case_module=$2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
host=$root/build/tools/leanexe-wasmtime-host
out=$root/build/verified
mkdir -p "$out"
cd "$root"
emitted=0
for entry in Verified.Examples.Poly:compiled.module:poly Verified.Examples.Mix:compiled.module:mix \
    Verified.Examples.Lets:compiled.module:lets Verified.Examples.Select:compiled.module:select \
    Verified.Examples.Calls:compiled.module:calls Verified.Examples.Pairs:compiled.module:pairs \
    Verified.Examples.Frontend:compiled.module:frontend \
    Verified.Examples.Fold:compiled.module:fold \
    Verified.Examples.TailCore:module:tailcore \
    Verified.Examples.Gpt:compiled.module:gpt \
    Verified.Examples.Euler:compiled.module:euler \
    Verified.Examples.Loops:compiled.module:loops \
    Verified.Examples.Arrays:compiled.module:arrays \
    Verified.Examples.Owned:compiled.module:owned \
    Verified.Examples.Updates:compiled.module:updates \
    Verified.Examples.Grow:compiled.module:grow \
    Verified.Examples.Modes:compiled.module:modes \
    Verified.Examples.Modes:byHandModule:byhand \
    Verified.Examples.Floats:compiled.module:floats \
    Verified.Examples.Elements:compiled.module:elements \
    Verified.Examples.Tuples:module:tuples \
    Verified.Examples.Records:compiled.module:records \
    Verified.Examples.Grids:compiled.module:grids \
    Verified.Examples.Repeat:compiled.module:repeat \
    Verified.Examples.Enums:compiled.module:enums \
    Verified.Examples.Recursion:compiled.module:recursion \
    Verified.Examples.Fields:compiled.module:fields \
    Verified.Examples.Trig:compiled.module:trig \
    Verified.Examples.Fourier:compiled.module:fourier \
    Verified.Examples.Insert:compiled.module:insert \
    Verified.Examples.Clob:compiled.module:clob \
    Verified.Examples.Tables:compiled.module:tables \
    Verified.Examples.Exp:compiled.module:exp Verified.Examples.Tanh:compiled.module:tanh \
    Verified.Examples.Log:compiled.module:log \
    Verified.Examples.Log1p:compiled.module:log1p Verified.Examples.Atan:compiled.module:atan \
    Verified.Examples.Asin:compiled.module:asin Verified.Examples.Tan:compiled.module:tan \
    Verified.Examples.Sinh:compiled.module:sinh Verified.Examples.Asinh:compiled.module:asinh \
    Verified.Examples.Exp2:compiled.module:exp2 Verified.Examples.Log2:compiled.module:log2 \
    Verified.Examples.Log10:compiled.module:log10 Verified.Examples.Pow:compiled.module:pow \
    Verified.Examples.Sinpi:compiled.module:sinpi Verified.Examples.Erf:compiled.module:erf \
    Verified.Examples.ParseFloat:compiled.module:parsefloat \
    Verified.Examples.PrintFloat:compiled.module:printfloat \
    Verified.Examples.Drone:compiled.module:drone \
    Verified.Examples.Lcg:compiled.module:lcg \
    Verified.Examples.ParkMiller:compiled.module:parkmiller \
    Verified.Examples.Xorshift:compiled.module:xorshift \
    Verified.Examples.Bessel:compiled.module:bessel Verified.Examples.Tgamma:compiled.module:tgamma \
    Verified.Examples.Lgamma:compiled.module:lgamma Verified.Examples.Erfc:compiled.module:erfc; do
  IFS=: read -r module constant name <<<"$entry"
  if [ -n "$case_module" ]; then
    [ "$name" = "$case_module" ] || continue
    tools/leanrun --timeout 15m lake build "$module"
  fi
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$module" "$module.$constant" \
    "$out/$name.wasm"
  wasm-tools validate "$out/$name.wasm"
  emitted=$((emitted + 1))
done
if [ "$emitted" -eq 0 ]; then
  echo "fail: unknown module $case_module" >&2
  exit 2
fi
if [ -z "$case_module" ] || [ "$case_module" = "gpt" ]; then
  tests/gpt/run.sh "$out/gpt.wasm"
  tests/gpt/sessions.sh "$out/gpt.wasm"
  if [ "$case_module" = "gpt" ]; then
    exit 0
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "euler" ]; then
  tests/modules/run.sh --module euler "$out/euler.wasm"
  if [ "$case_module" = "euler" ]; then
    exit 0
  fi
fi
# Each entry names the written module, the theorem module, and the file theorem module.  The file
# module's second theorem depends on every byte theorem of the module, so its axiom report covers
# them all.
if [ -z "$case_module" ]; then
for entry in exp:ExpTheorem:ExpFile log:LogTheorem:LogFile exp2:Exp2Bytes:Exp2File \
    trig:TrigTheorem:TrigFile log2:Log2Theorem:Log2File log10:Log10Theorem:Log10File \
    tanh:TanhBytes:TanhFile erf:ErfTheorem:ErfFile log1p:Log1pBytes:Log1pFile \
    atan:AtanBytes:AtanFile asin:AsinBytes:AsinFile tan:TanTheorem:TanFile \
    sinh:SinhBytes:SinhFile sinpi:SinpiTheorem:SinpiFile asinh:AsinhBytes:AsinhFile \
    pow:PowBytes:PowFile parsefloat:ParseFloatBytes:ParseFloatFile \
    printfloat:PrintFloatBytes:PrintFloatFile \
    bessel:BesselBytes:BesselFile tgamma:TgammaBytes:TgammaFile lgamma:LgammaBytes:LgammaFile \
    erfc:ErfcBytes:ErfcFile; do
  IFS=: read -r name theorem file <<<"$entry"
  tools/leanrun --timeout 30m lake build "Verified.Examples.$theorem"
  reports=$(tools/leanrun --timeout 10m lake env lean "Verified/Examples/$file.lean") || {
    echo "$reports"
    echo "fail: Verified/Examples/$file.lean does not check against $out/$name.wasm" >&2
    exit 1
  }
  permitted=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" \
    <<<"$reports" || true)
  if [ "$permitted" -ne 2 ]; then
    echo "$reports"
    echo "fail: the theorems of $file.lean must report only the three permitted axioms" >&2
    exit 1
  fi
  echo "$name: $name.wasm holds the module of Verified.Examples.$theorem, with the permitted axioms"
done
fi
tools/leanrun --timeout 30m lake build Verified.Examples.Cases
cases=$(mktemp)
errors=$(mktemp)
trap 'rm -f "$cases" "$errors"' EXIT
# Native Lean panics on the reads and updates past the end of an array that the cases exercise: it
# writes a message and a backtrace to standard error.  A read returns Lean's default element,
# an update the array unchanged, and insertIdx! an empty array.  The run fails when Lean exits
# with an error or writes any other message.
if ! tools/leanrun --timeout 10m lake env lean --run Verified/Examples/Cases.lean \
    >"$cases" 2>"$errors"; then
  cat "$errors" >&2
  echo "fail: native Lean exited with an error" >&2
  exit 1
fi
counts=$(awk '
  $0 == "Error: index out of bounds" { reads++; next }
  /^PANIC at Array\.insertIdx! Init\.Data\.Array\.Basic:[0-9]+:[0-9]+: invalid index$/ { inserts++; next }
  $0 == "backtrace:" || /\[0x[0-9a-f]+\]$/ { next }
  { others++; print > "/dev/stderr" }
  END { print reads + 0, inserts + 0, others + 0 }' "$errors")
read -r reads inserts others <<<"$counts"
if [ "$others" -ne 0 ]; then
  echo "fail: native Lean wrote $others unexpected lines to standard error, shown above" >&2
  exit 1
fi
echo "native Lean: $reads accesses past the end and $inserts insertIdx! past the end, as the cases expect"
passed=0
failed=0
while IFS='|' read -r name export result args expected live allocsMax; do
  if [ -n "$case_module" ] && [ "$name" != "$case_module" ]; then
    continue
  fi
  read -ra argv <<<"$args"
  if [ "$expected" = "trap" ]; then
    if "$host" call "$out/$name.wasm" "$export" "$result" "${argv[@]}" >/dev/null 2>"$errors"; then
      failed=$((failed + 1))
      echo "fail: $name $export $args: returned, expected a trap at unreachable"
    elif grep -q 'wasm `unreachable` instruction executed' "$errors"; then
      passed=$((passed + 1))
    else
      failed=$((failed + 1))
      echo "fail: $name $export $args: $(cat "$errors"), expected a trap at unreachable"
    fi
    continue
  fi
  if [ -z "$live" ]; then
    got=$("$host" call "$out/$name.wasm" "$export" "$result" "${argv[@]}" | paste -sd' ')
    held=""
  else
    output=$("$host" call-stats "$out/$name.wasm" "$export" "$result" "${argv[@]}")
    got=$(sed '$d' <<<"$output" | paste -sd' ')
    read -r _ allocs frees < <(tail -n 1 <<<"$output")
    held=$((allocs - frees))
  fi
  if [ -n "$allocsMax" ] && [ "$allocs" -gt "$allocsMax" ]; then
    failed=$((failed + 1))
    echo "fail: $name $export $args: $allocs allocations, at most $allocsMax expected"
  elif [ "$got" = "$expected" ] && [ "$held" = "$live" ]; then
    passed=$((passed + 1))
  else
    failed=$((failed + 1))
    echo "fail: $name $export $args: $got, expected $expected; live blocks $held, expected $live"
  fi
done <"$cases"
echo "verified: passed $passed failed $failed"
[ "$passed" -gt 0 ] && [ "$failed" -eq 0 ] || exit 1
if [ -n "$case_module" ]; then
  exit 0
fi
# The accuracy of Trig.sin and Trig.cos against a reference computed with Lean's integers, in
# native Lean.
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/TrigAccuracy.lean || exit 1
# The behavior of the Fourier transforms, in native Lean.
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/FourierAccuracy.lean || exit 1
# The accuracy of exp, expm1, tanh, log, log1p, atan, atan2, asin, acos, tan, sinh, cosh, asinh,
# acosh, atanh, exp2, exp10, log2, log10, pow, sinpi, cospi, tanpi, erf, and erfc against
# references computed with Lean's integers, in native Lean.
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/ExpAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/TanhAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/LogAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/Log1pAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/AtanAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/AsinAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/TanAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/SinhAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/AsinhAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/Exp2Accuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/Log2Accuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/PowAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/SinpiAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/ErfAccuracy.lean || exit 1
# The accuracy of tgamma, lgamma, the Bessel functions, and CORE-MATH's erfc against references
# computed with Lean's integers, in native Lean.
tools/leanrun --timeout 30m lake env lean --run Verified/Examples/TgammaAccuracy.lean || exit 1
tools/leanrun --timeout 30m lake env lean --run Verified/Examples/LgammaAccuracy.lean || exit 1
tools/leanrun --timeout 30m lake env lean --run Verified/Examples/BesselAccuracy.lean || exit 1
tools/leanrun --timeout 30m lake env lean --run Verified/Examples/ErfcAccuracy.lean || exit 1
# The software fused multiply-add against the exact value rounded to the nearest double, in native
# Lean.
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/FmaAccuracy.lean || exit 1
# The limb arithmetic of the string conversions against Lean's natural numbers, in native Lean.
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/UscaleCheck.lean || exit 1
# The decimal parsers and printers against references computed with Lean's integers, in native Lean.
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/ParseFloatAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run Verified/Examples/PrintFloatAccuracy.lean || exit 1
