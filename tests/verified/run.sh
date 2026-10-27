#!/usr/bin/env bash
# Writes the modules of the verified compiler's examples, validates them with wasm-tools, and
# compares their checked cases between the Wasmtime host and native Lean.
# A case with a sixth field also checks the allocation counters: the blocks allocated less those
# released must equal the field, the result's arrays and the host's arrays at borrowed parameters.
# A seventh field bounds the number of allocations, the host's included.  A case whose expected
# result is `trap` must trap at `unreachable`.  After writing the modules, it builds each function's
# theorem module and checks its file theorem module, whose theorems state that the written file
# holds the module of the function's byte theorem, and it fails unless both file theorems report
# only the axioms propext, Classical.choice, and Quot.sound.  For the slew planner, it also compares
# the edgeOk export with native Lean and runs the axiom audit of tests/slew/Axioms.lean, and with
# --cases slew it checks the planner's file theorem module as well.  Last, the
# tests/TestSupport/Numerics/*Accuracy.lean checks compare the transcendental functions with
# references computed with Lean's integers, each within the bound its docstring states, and
# tests/TestSupport/Numerics/FourierAccuracy.lean checks that Fourier.dft, inverse, and
# powerSpectrum behave as their mathematical counterparts.
# Run `tools/leanrun --timeout 60m lake build`, whose default targets include the module cases of
# the Euler check, and `tools/leanrun --threads 2 --memory-high 10G --timeout 12h lake build Verified
# Library` first.
# Usage: tests/verified/run.sh [--cases MODULE | --check-bytes DIRECTORY]
set -euo pipefail
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"
case_module=""
reference=""
if [ "$#" -ne 0 ]; then
  if [ "$#" -ne 2 ] || [ -z "$2" ]; then
    echo "usage: tests/verified/run.sh [--cases MODULE | --check-bytes DIRECTORY]" >&2
    exit 2
  fi
  case "$1" in
    --cases) case_module=$2 ;;
    --check-bytes) reference=$(cd "$2" && pwd -P) ;;
    *) echo "usage: tests/verified/run.sh [--cases MODULE | --check-bytes DIRECTORY]" >&2; exit 2 ;;
  esac
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
host=$root/build/tools/leanexe-wasmtime-host
out=$root/build/verified
if [ -n "$reference" ]; then out=$root/build/byte-check/verified; fi
mkdir -p "$out"
if [ "$reference" = "$(cd "$out" && pwd -P)" ]; then
  echo "fail: byte reference and emission directories must differ" >&2
  exit 2
fi
cd "$root"
emitted=0
while IFS=: read -r module constant name; do
  if [ -n "$case_module" ]; then
    [ "$name" = "$case_module" ] || continue
    tools/leanrun --timeout 15m lake --log-level error build "$module"
  fi
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$module" "$constant" \
    "$out/$name.wasm"
  wasm-tools validate "$out/$name.wasm"
  if [ -n "$reference" ]; then
    cmp "$reference/$name.wasm" "$out/$name.wasm"
    echo "$name: bytes unchanged"
  fi
  emitted=$((emitted + 1))
done <"$root/tests/verified/modules.txt"
if [ "$emitted" -eq 0 ]; then
  echo "fail: unknown module $case_module" >&2
  exit 2
fi
if [ -n "$reference" ]; then
  echo "verified byte comparison passed: $emitted modules"
  exit 0
fi
if [ ! -x "$host" ] || [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  echo "fail: $host is missing or older than tools/wasmtime-host.c; build it with tools/build-wasmtime-host.sh" >&2
  exit 1
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
if [ -z "$case_module" ] || [ "$case_module" = "sums" ]; then
  tests/modules/run.sh --module shapes "$out/sums.wasm"
fi
# Checks the file theorem module of a written module: builds the theorem module, elaborates the file
# module against the file, and requires both of its axiom reports to name only the three permitted
# axioms.  The file module's second theorem depends on every byte theorem of the module, so its
# axiom report covers them all.
check_file() {
  local name=$1 theorem=$2 file=$3 reports axiom_counts
  tools/leanrun --timeout 30m lake --log-level error build "$theorem"
  reports=$(tools/leanrun --timeout 10m lake env lean "$file") || {
    echo "$reports"
    echo "fail: $file does not check against $out/$name.wasm" >&2
    exit 1
  }
  axiom_counts=$(awk '
    /depends on axioms: \[/ {
      report = $0
      while (report !~ /\]/ && (getline) > 0) report = report " " $0
      sub(/^.*depends on axioms: /, "", report)
      gsub(/[[:space:]]+/, " ", report)
      count++
      if (report == "[propext, Classical.choice, Quot.sound]") permitted++
    }
    END { print count + 0, permitted + 0 }' <<<"$reports")
  if [ "$axiom_counts" != "2 2" ]; then
    echo "$reports"
    echo "fail: the theorems of $file must report only the three permitted axioms" >&2
    exit 1
  fi
  echo "$name: $name.wasm holds the module of $theorem, with the permitted axioms"
}
if [ -z "$case_module" ] || [ "$case_module" = "slew" ]; then
  tests/slew/edges.sh "$out/slew.wasm"
  tools/leanrun --timeout 60m lake --log-level error build Demos.Slew.Optimal Demos.Slew.Premise \
    Demos.Slew.Bound
  tools/leanrun --timeout 10m lake env lean tests/slew/Axioms.lean
  if [ "$case_module" = "slew" ]; then
    check_file slew Demos.Slew.Verified Demos/Slew/File.lean
  fi
fi
# Each entry names the written module, the theorem module, and the file theorem module.
if [ -z "$case_module" ]; then
while IFS=: read -r name theorem file; do
  check_file "$name" "$theorem" "$file"
done <"$root/tests/verified/numerics.txt"
fi
cases_module=Verified.Examples.Cases
cases_source=Verified/Examples/Cases.lean
if [ "$case_module" = "treecopy" ]; then
  cases_module=Verified.Examples.TreeCopyCasesMain
  cases_source=Verified/Examples/TreeCopyCasesMain.lean
elif [ "$case_module" = "treecore" ]; then
  cases_module=Verified.Examples.TreeCasesMain
  cases_source=Verified/Examples/TreeCasesMain.lean
elif [ "$case_module" = "lists" ]; then
  cases_module=Verified.Examples.ListsCasesMain
  cases_source=Verified/Examples/ListsCasesMain.lean
elif [ "$case_module" = "composition" ]; then
  cases_module=Verified.Examples.CompositionCasesMain
  cases_source=Verified/Examples/CompositionCasesMain.lean
elif [ "$case_module" = "scalarcomposition" ]; then
  cases_module=Verified.Examples.ScalarCompositionCasesMain
  cases_source=Verified/Examples/ScalarCompositionCasesMain.lean
elif [ "$case_module" = "relocation" ]; then
  cases_module=Verified.Examples.RelocationCasesMain
  cases_source=Verified/Examples/RelocationCasesMain.lean
elif [ "$case_module" = "wgsl" ]; then
  cases_module=Verified.Examples.WgslWasmCasesMain
  cases_source=Verified/Examples/WgslWasmCasesMain.lean
elif [ "$case_module" = "gpt32" ]; then
  cases_module=Demos.Gpt32.VerifiedWasmCasesMain
  cases_source=Demos/Gpt32/VerifiedWasmCasesMain.lean
elif [ "$case_module" = "listrecursion" ]; then
  cases_module=Verified.Examples.ListRecursionCasesMain
  cases_source=Verified/Examples/ListRecursionCasesMain.lean
elif [ "$case_module" = "listloops" ]; then
  cases_module=Verified.Examples.ListLoopsCasesMain
  cases_source=Verified/Examples/ListLoopsCasesMain.lean
elif [ "$case_module" = "listtail" ]; then
  cases_module=Verified.Examples.ListTailCasesMain
  cases_source=Verified/Examples/ListTailCasesMain.lean
elif [ "$case_module" = "recursivetypes" ]; then
  cases_module=Verified.Examples.RecursiveTypesCasesMain
  cases_source=Verified/Examples/RecursiveTypesCasesMain.lean
elif [ "$case_module" = "sha256" ]; then
  cases_module=TestSupport.Hashing.Sha256CasesMain
  cases_source=tests/TestSupport/Hashing/Sha256CasesMain.lean
elif [ "$case_module" = "sha512" ]; then
  cases_module=TestSupport.Hashing.Sha512CasesMain
  cases_source=tests/TestSupport/Hashing/Sha512CasesMain.lean
elif [ "$case_module" = "hmac_sha256" ] || [ "$case_module" = "hmac_sha512" ]; then
  cases_module=TestSupport.Hashing.HmacCasesMain
  cases_source=tests/TestSupport/Hashing/HmacCasesMain.lean
elif [ "$case_module" = "taggedtypes" ]; then
  cases_module=Verified.Examples.TaggedTypesCasesMain
  cases_source=Verified/Examples/TaggedTypesCasesMain.lean
elif [ "$case_module" = "heapsums" ]; then
  cases_module=Verified.Examples.HeapSumsCasesMain
  cases_source=Verified/Examples/HeapSumsCasesMain.lean
elif [ "$case_module" = "regex" ]; then
  cases_module=TestSupport.Regex.CasesMain
  cases_source=tests/TestSupport/Regex/CasesMain.lean
elif [ "$case_module" = "sha3" ]; then
  cases_module=TestSupport.Hashing.Sha3CasesMain
  cases_source=tests/TestSupport/Hashing/Sha3CasesMain.lean
elif [ "$case_module" = "crc" ]; then
  cases_module=TestSupport.Hashing.CrcCasesMain
  cases_source=tests/TestSupport/Hashing/CrcCasesMain.lean
elif [ "$case_module" = "siphash" ]; then
  cases_module=TestSupport.Hashing.SipHashCasesMain
  cases_source=tests/TestSupport/Hashing/SipHashCasesMain.lean
elif [ "$case_module" = "xxhash64" ]; then
  cases_module=TestSupport.Hashing.XxHash64CasesMain
  cases_source=tests/TestSupport/Hashing/XxHash64CasesMain.lean
elif [ "$case_module" = "slew" ]; then
  cases_module=TestSupport.Slew.CasesMain
  cases_source=tests/TestSupport/Slew/CasesMain.lean
fi
if [ -z "$case_module" ] || [ "$case_module" = "heapsums" ]; then
  tools/leanrun --timeout 10m lake env lean tests/verified/HeapSumsAxioms.lean
fi
tools/leanrun --timeout 30m lake --log-level error build "$cases_module"
cases=$(mktemp)
errors=$(mktemp)
trap 'rm -f "$cases" "$errors"' EXIT
# Native Lean panics on the reads and updates past the end of an array that the cases exercise: it
# writes a message and a backtrace to standard error.  A read returns Lean's default element,
# an update the array unchanged, and insertIdx! an empty array.  The run fails when Lean exits
# with an error or writes any other message.
if ! tools/leanrun --timeout 10m lake env lean --run "$cases_source" \
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
awk -F'|' '
  BEGIN { OFS = FS }
  NR == FNR { targets[$1 FS $2] = $3 FS $4; next }
  { print; key = $1 FS $2 }
  key in targets {
    split(targets[key], target, FS)
    $1 = target[1]; $2 = target[2]; print
  }' "$root/tests/verified/library-cases.txt" "$cases" >"$cases.library"
mv "$cases.library" "$cases"
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
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/TrigAccuracy.lean || exit 1
# The behavior of the Fourier transforms, in native Lean.
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/FourierAccuracy.lean || exit 1
# The accuracy of exp, expm1, tanh, log, log1p, atan, atan2, asin, acos, tan, sinh, cosh, asinh,
# acosh, atanh, exp2, exp10, log2, log10, pow, sinpi, cospi, tanpi, erf, and erfc against
# references computed with Lean's integers, in native Lean.
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/ExpAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/TanhAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/LogAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/Log1pAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/AtanAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/AsinAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/TanAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/SinhAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/AsinhAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/Exp2Accuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/Log2Accuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/PowAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/SinpiAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/ErfAccuracy.lean || exit 1
# The accuracy of tgamma, lgamma, the Bessel functions, and CORE-MATH's erfc against references
# computed with Lean's integers, in native Lean.
tools/leanrun --timeout 30m lake env lean --run tests/TestSupport/Numerics/TgammaAccuracy.lean || exit 1
tools/leanrun --timeout 30m lake env lean --run tests/TestSupport/Numerics/LgammaAccuracy.lean || exit 1
tools/leanrun --timeout 30m lake env lean --run tests/TestSupport/Numerics/BesselAccuracy.lean || exit 1
tools/leanrun --timeout 30m lake env lean --run tests/TestSupport/Numerics/ErfcAccuracy.lean || exit 1
# The software fused multiply-add against the exact value rounded to the nearest double, in native
# Lean.
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/FmaAccuracy.lean || exit 1
# The limb arithmetic of the string conversions against Lean's natural numbers, in native Lean.
tools/leanrun --timeout 10m lake env lean --run Library/Numerics/Arithmetic/Uscale/UscaleCheck.lean || exit 1
# The decimal parsers and printers against references computed with Lean's integers, in native Lean.
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/ParseFloatAccuracy.lean || exit 1
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Numerics/PrintFloatAccuracy.lean || exit 1
