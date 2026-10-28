#!/usr/bin/env bash
# The cases of tests/verified, run on the modules translated to C and compiled with CompCert.
# For each module of tests/verified/modules.txt, native-verified build (tests/TestSupport/Native/
# Verified.lean) writes the C text of its translation, the glue of tools/native-host.h, and the
# exports that the translation contains, has clightgen read the C text back, compares that Clight
# with the translation, and compiles the text with ccomp only when they match.  ccomp then links
# the object with the glue and tools/native-host.c, which takes the commands of the Wasmtime host.  The cases are the
# lines of the compiled generator verified-cases (Verified/Examples/Cases.lean), with the library
# entries of tests/verified/library-cases.txt, which tests/verified/run.sh checks with Wasmtime.
# A case runs when the translation contains its export, and a module outside the subset, which
# has no translation, runs none of its cases.  A case that runs must give the line that the
# Wasmtime host gives, with the same rules for traps and allocation counters.  The module cases
# of tests/modules/Cases.lean that tests/verified/run.sh checks for the corpus, those of euler
# and of shapes on sums, come from the compiled generator native-module-cases
# (tests/TestSupport/Native/ModuleCases.lean) and run the same way under the rules of
# tests/modules/run.sh.  The script prints the numbers of cases that pass, that fail, and that do
# not run, and fails unless every case that runs passes.  Before it loads any module, it builds
# every module it loads and the executables it runs in one `lake build` under tools/leanrun, with
# the caller's LEANRUN_THREADS and LEANRUN_MEMORY_HIGH, since native-verified reads a module's
# compiled file without checking it against the source.  CCOMP, CLIGHTGEN, and CCOMP_STDLIB are
# as for tests/native/run.sh.
# LEANRUN_MEMORY_HIGH is the memory limit of each step that runs under tools/leanrun, 6G unless
# the caller sets it.  The largest step measured, native-verified build of the largest corpus
# module, keeps 3.7 GB resident.
# Usage: tests/native/verified.sh [--module NAME]
set -euo pipefail
export LEANRUN_MEMORY_HIGH=${LEANRUN_MEMORY_HIGH:-6G}
only=""
if [ "$#" -ne 0 ]; then
  if [ "$#" -ne 2 ] || [ "$1" != "--module" ] || [ -z "$2" ]; then
    echo "usage: tests/native/verified.sh [--module NAME]" >&2
    exit 2
  fi
  only=$2
fi
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$root/build/native/verified
cd "$root"
targets=(native-verified verified-cases native-module-cases)
while IFS=: read -r module constant name; do
  if [ -z "$only" ] || [ "$name" = "$only" ]; then
    targets+=("$module")
  fi
done <"$root/tests/verified/modules.txt"
tools/leanrun --timeout 12h lake --log-level error build "${targets[@]}"
rm -rf "$out"
mkdir -p "$out"
modules=0
untranslated=""
while IFS=: read -r module constant name; do
  if [ -n "$only" ] && [ "$name" != "$only" ]; then
    continue
  fi
  modules=$((modules + 1))
  status=0
  CLIGHTGEN=$clightgen CCOMP=$ccomp tools/leanrun --timeout 10m lake env \
    .lake/build/bin/native-verified build "$module" "$constant" "$name" "$out" || status=$?
  if [ "$status" -eq 3 ]; then
    untranslated="$untranslated $name"
    continue
  elif [ "$status" -ne 0 ]; then
    exit "$status"
  fi
  "$ccomp" "${stdlib[@]}" -I "$root/tools" -o "$out/$name" "$out/$name.o" "$out/${name}_glue.c" \
    "$root/tools/native-host.c"
done <"$root/tests/verified/modules.txt"
if [ "$modules" -eq 0 ]; then
  echo "fail: unknown module $only" >&2
  exit 2
fi
cases=$out/cases.txt
errors=$out/errors.txt
# Native Lean writes the panics that the cases exercise to standard error, which
# tests/verified/run.sh checks; here only its exit status counts.
if ! tools/leanrun --timeout 10m .lake/build/bin/verified-cases >"$cases" 2>"$out/cases.err"; then
  cat "$out/cases.err" >&2
  echo "fail: native Lean exited with an error" >&2
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
passed=0
failed=0
omitted=0
others=0
while IFS='|' read -r name export result args expected live allocsMax; do
  if [ -n "$only" ] && [ "$name" != "$only" ]; then
    continue
  fi
  if [ ! -f "$out/$name.exports" ]; then
    others=$((others + 1))
    continue
  fi
  if ! grep -qxF "$export" "$out/$name.exports"; then
    omitted=$((omitted + 1))
    continue
  fi
  read -ra argv <<<"$args"
  host=$out/$name
  if [ "$expected" = "trap" ]; then
    if "$host" call "$export" "$result" "${argv[@]}" >/dev/null 2>"$errors"; then
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
  allocs=""
  if [ -z "$live" ]; then
    if ! output=$("$host" call "$export" "$result" "${argv[@]}" 2>"$errors"); then
      failed=$((failed + 1))
      echo "fail: $name $export $args: $(cat "$errors"), expected $expected"
      continue
    fi
    got=$(paste -sd' ' <<<"$output")
    held=""
  else
    if ! output=$("$host" call-stats "$export" "$result" "${argv[@]}" 2>"$errors"); then
      failed=$((failed + 1))
      echo "fail: $name $export $args: $(cat "$errors"), expected $expected"
      continue
    fi
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
echo "native verified: passed $passed failed $failed"
echo "native verified: not run: $omitted outside the translation, $others of modules without a translation"
echo "native verified: modules without a translation:${untranslated:- none}"
modcases=$out/module-cases.txt
if ! tools/leanrun --timeout 10m .lake/build/bin/native-module-cases \
    >"$modcases" 2>"$out/module-cases.err"; then
  cat "$out/module-cases.err" >&2
  echo "fail: native Lean exited with an error" >&2
  exit 1
fi
mpassed=0
mfailed=0
momitted=0
while IFS='|' read -r module name result args expected; do
  case "$module" in
    euler) prog=euler ;;
    shapes) prog=sums ;;
    *) continue ;;
  esac
  if [ -n "$only" ] && [ "$prog" != "$only" ]; then
    continue
  fi
  if [ ! -f "$out/$prog.exports" ] || ! grep -qxF "$name" "$out/$prog.exports"; then
    momitted=$((momitted + 1))
    continue
  fi
  read -ra argv <<<"$args"
  if got=$("$out/$prog" call "$name" "$result" "${argv[@]}" 2>"$errors" | tr -d '[] ' |
      paste -sd, -) && [ "$got" = "$expected" ]; then
    mpassed=$((mpassed + 1))
  else
    mfailed=$((mfailed + 1))
    echo "fail: $module $name $args: $got $(cat "$errors"), expected $expected"
  fi
done <"$modcases"
echo "native modules: passed $mpassed failed $mfailed"
echo "native modules: not run: $momitted outside the translation"
[ "$passed" -gt 0 ] && [ "$failed" -eq 0 ] && [ "$mfailed" -eq 0 ]
