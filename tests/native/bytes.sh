#!/usr/bin/env bash
# The byte and literal examples translated to C.  native-verified build translates
# Verified.Examples.Bytes and Verified.Examples.Literals, has clightgen read each C text back,
# compares that Clight with the translation, and compiles the text with ccomp only when they
# match; ccomp then links the object with its glue and tools/native-host.c.  The cases of tests/wasi/bytes.tsv,
# tests/wasi/literals.tsv, and tests/wasi/byte-traps.tsv, which tests/wasi/run.sh checks with
# Wasmtime, must give the same lines and allocation counts natively, and each trap case must stop
# at `unreachable`.  The build includes tests/TestSupport/Native/LiteralsNative.lean, which states
# the examples' native theorems.  CCOMP, CLIGHTGEN, and CCOMP_STDLIB are as for
# tests/native/run.sh.
# LEANRUN_MEMORY_HIGH is the memory limit of each step that runs under tools/leanrun, 6G unless
# the caller sets it.  The largest step measured, the elaboration of the native theorem file
# that the build compiles, keeps 3.7 GB resident.
# Usage: tests/native/bytes.sh
set -euo pipefail
export LEANRUN_MEMORY_HIGH=${LEANRUN_MEMORY_HIGH:-6G}
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$root/build/native/bytes
cd "$root"
tools/leanrun --timeout 60m lake build native-verified TestSupport.Native.LiteralsNative
rm -rf "$out"
mkdir -p "$out"
for name in Bytes Literals; do
  module=Verified.Examples.$name
  lower=$(printf '%s' "$name" | tr '[:upper:]' '[:lower:]')
  CLIGHTGEN=$clightgen CCOMP=$ccomp tools/leanrun --timeout 10m lake env \
    .lake/build/bin/native-verified build "$module" "$module.compiled.module" "$lower" "$out"
  "$ccomp" "${stdlib[@]}" -I "$root/tools" -o "$out/$lower" "$out/$lower.o" \
    "$out/${lower}_glue.c" "$root/tools/native-host.c"
done
tab=$(printf '\t')
status=0
check_cases() {
  local program=$1 file=$2 label=$3 count=0 failed=0
  local export_name kind arguments expected allocations releases observed wanted
  while IFS="$tab" read -r export_name kind arguments expected allocations releases; do
    if [ "$expected" = _ ]; then expected=; fi
    local args=()
    if [ "$arguments" != _ ]; then read -r -a args <<<"$arguments"; fi
    observed=$("$program" call-stats "$export_name" "$kind" "${args[@]}") || true
    wanted=$(printf '%s\nstats %s %s' "$expected" "$allocations" "$releases")
    if [ "$observed" != "$wanted" ]; then
      printf 'fail: %s %s %s: %s, expected %s\n' "$label" "$export_name" "$arguments" \
        "$observed" "$wanted" >&2
      failed=$((failed + 1))
    fi
    count=$((count + 1))
  done <"$file"
  echo "native bytes: $label: $((count - failed)) of $count cases agree with Wasmtime"
  if [ "$failed" -ne 0 ]; then status=1; fi
}
check_cases "$out/bytes" "$root/tests/wasi/bytes.tsv" bytes
check_cases "$out/literals" "$root/tests/wasi/literals.tsv" literals
count=0
while IFS="$tab" read -r export_name arguments; do
  read -r -a args <<<"$arguments"
  if "$out/bytes" call "$export_name" bytes "${args[@]}" >"$out/trap-$count.log" 2>&1; then
    echo "fail: $export_name $arguments: returned, expected a trap at unreachable" >&2
    status=1
  elif ! grep -q unreachable "$out/trap-$count.log"; then
    echo "fail: $export_name $arguments: $(cat "$out/trap-$count.log"), expected unreachable" >&2
    status=1
  fi
  count=$((count + 1))
done <"$root/tests/wasi/byte-traps.tsv"
echo "native bytes: $count trap cases run"
exit $status
