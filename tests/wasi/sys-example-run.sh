#!/bin/sh
# Builds the flat call example and its total theorem, Verified.Examples.WasiSysTotal, checks their
# axioms and the witness host, for which tests/wasi/SysWitness.lean applies the total theorem, runs
# its native cases, and runs its module in the Wasmtime host with several argument lists.  Each
# run must exit with status 0 and write the arguments with a zero byte after each, the argument
# count and size as 8 little-endian bytes each, a realtime reading within a day of the system clock,
# a monotonic reading below 10^17 ns, and 16 random bytes.  Four runs with the same arguments must
# give at least two values at each of the 16 random positions, which a correct module fails with
# probability at most 2^-20.  It then builds the example with input calls,
# Verified.Examples.WasiSysInputs, checks its axioms with tests/wasi/SysInputs.lean, and runs its
# module with a fresh preopened directory: the run must exit with status 0 and leave the directory
# empty.  Last it builds the example with record calls, Verified.Examples.WasiSysRecords, checks its
# axioms with tests/wasi/SysRecordAxioms.lean, runs the native cases of the record typed functions
# in tests/wasi/SysRecords.lean, and runs its module with a fresh preopened directory.  The run must
# exit with status 0, leave the directory empty, and write the fields of its records as 34 words of
# 8 little-endian bytes, among them the prestat tag 0 and name length 1, the directory's file type
# 3 in its fdstat and its filestat, the file type 4 and the append flag 1 in the created file's
# fdstat, and the file type 4 and the size 2^32 + 5 in its filestat, which must be the same through
# the descriptor and through the path.
set -eu
set -f
if ! command -v wasm-tools > /dev/null 2>&1; then
  printf 'wasm-tools is not on the search path\n' >&2
  exit 1
fi

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
out="$root/build/wasi/sys-example"
host="$root/build/tools/leanexe-wasmtime-host"
module="$out/sys.wasm"
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi

tools/leanrun --timeout 30m --log "$out/build.log" lake build Verified.Examples.WasiSys \
  Verified.Examples.WasiSysTotal Verified.Examples.WasiSysInputs Verified.Examples.WasiSysRecords
tools/leanrun --timeout 5m lake env lean tests/wasi/SysAxioms.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/SysWitness.lean
tools/leanrun --timeout 10m lake env lean tests/wasi/SysInputs.lean
tools/leanrun --timeout 10m lake env lean tests/wasi/SysRecordAxioms.lean
tools/leanrun --timeout 5m lake env lean --run tests/wasi/SysExample.lean
tools/leanrun --timeout 5m lake env lean --run tests/wasi/SysRecords.lean
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiSys \
  Verified.Examples.WasiSys.command.module "$module"
wasm-tools validate "$module"

fail() {
  printf 'flat call example %s: %s\n' "$1" "$2" >&2
  exit 1
}

# word FILE OFFSET: the unsigned little-endian 8-byte word at OFFSET, in decimal.
word() {
  od -An -v -t u1 -j "$2" -N 8 "$1" |
    awk '{ for (i = 1; i <= NF; i++) b[n++] = $i } END {
      v = 0; for (i = 7; i >= 0; i--) v = v * 256 + b[i]; printf "%.0f\n", v }'
}

cases=0

# check NAME COUNT EXPECTED: the output of the run NAME, whose arguments were COUNT strings with
# the bytes of EXPECTED, a file holding each argument followed by a zero byte.
check() {
  name=$1 count=$2 expected=$3
  stdout="$out/$name.stdout"
  size=$(wc -c < "$expected")
  written=$(wc -c < "$stdout")
  [ "$written" -eq $((size + 48)) ] || fail "$name" "wrote $written bytes"
  head -c "$size" "$stdout" | cmp -s - "$expected" || fail "$name" "wrong argument bytes"
  [ "$(word "$stdout" "$size")" = "$count" ] || fail "$name" "count $(word "$stdout" "$size")"
  [ "$(word "$stdout" $((size + 8)))" = "$size" ] || fail "$name" "size"
  wall=$(word "$stdout" $((size + 16)))
  now=$(date +%s)
  awk -v wall="$wall" -v now="$now" 'BEGIN { d = wall / 1e9 - now; exit !(d < 86400 && d > -86400) }' ||
    fail "$name" "realtime reading $wall at $now s"
  mono=$(word "$stdout" $((size + 24)))
  awk -v mono="$mono" 'BEGIN { exit !(mono < 1e17) }' || fail "$name" "monotonic reading $mono"
  printf 'wasi-exit 0\n' | cmp -s - "$out/$name.control" || fail "$name" "control"
  cases=$((cases + 1))
}

# run NAME ARG...: runs the module with the arguments ARG.
run() {
  name=$1
  shift
  status=0
  timeout 60s "$host" "$@" --stdout-file "$out/$name.stdout" --control-file "$out/$name.control" \
    run "$module" 2> "$out/$name.stderr" || status=$?
  [ "$status" -eq 0 ] || fail "$name" "status $status"
}

printf '' > "$out/none.expected"
run none
check none 0 "$out/none.expected"

printf 'prog\000' > "$out/one.expected"
for repeat in 1 2 3 4; do
  run "one-$repeat" --arg prog
  check "one-$repeat" 1 "$out/one.expected"
done
for repeat in 1 2 3 4; do
  od -An -v -t u1 -j 37 -N 16 "$out/one-$repeat.stdout"
done | awk '{ for (i = 1; i <= NF; i++) seen[i, $i] = 1 }
  END { for (i = 1; i <= 16; i++) { n = 0; for (k in seen) { split(k, p, SUBSEP); if (p[1] == i) n++ }
    if (n < 2) exit 1 } }' || fail "random" "a random position kept one value in four runs"
cases=$((cases + 1))

printf 'prog\000a\000b c\000\000' > "$out/four.expected"
run four --arg prog --arg a --arg "b c" --arg ""
check four 4 "$out/four.expected"

long=$(head -c 4096 /dev/zero | tr '\0' x)
printf 'prog\000%s\000' "$long" > "$out/long.expected"
run long --arg prog --arg "$long"
check long 2 "$out/long.expected"

inputs="$out/inputs.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiSysInputs \
  Verified.Examples.WasiSysInputs.command.module "$inputs"
wasm-tools validate "$inputs"
rm -rf "$out/inputs-dir"
mkdir "$out/inputs-dir"
status=0
timeout 60s "$host" --dir "$out/inputs-dir" --stdout-file "$out/inputs.stdout" \
  --control-file "$out/inputs.control" run "$inputs" 2> "$out/inputs.stderr" || status=$?
[ "$status" -eq 0 ] || fail inputs "status $status"
printf 'wasi-exit 0\n' | cmp -s - "$out/inputs.control" || fail inputs "control"
[ -z "$(ls -A "$out/inputs-dir")" ] || fail inputs "the directory is not empty"
cases=$((cases + 1))

records="$out/records.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiSysRecords \
  Verified.Examples.WasiSysRecords.command.module "$records"
wasm-tools validate "$records"
rm -rf "$out/records-dir"
mkdir "$out/records-dir"
status=0
timeout 60s "$host" --dir "$out/records-dir" --stdout-file "$out/records.stdout" \
  --control-file "$out/records.control" run "$records" 2> "$out/records.stderr" || status=$?
[ "$status" -eq 0 ] || fail records "status $status"
printf 'wasi-exit 0\n' | cmp -s - "$out/records.control" || fail records "control"
[ -z "$(ls -A "$out/records-dir")" ] || fail records "the directory is not empty"
written=$(wc -c < "$out/records.stdout")
[ "$written" -eq 272 ] || fail records "wrote $written bytes"
# field INDEX NAME VALUE: word INDEX of the output, the field NAME, must be VALUE.
field() {
  value=$(word "$out/records.stdout" $(($1 * 8)))
  [ "$value" = "$3" ] || fail records "$2 is $value, expected $3"
}
field 0 "the prestat tag" 0
field 1 "the prestat name length" 1
field 2 "the directory's fdstat file type" 3
field 8 "the directory's filestat file type" 3
field 14 "the file's fdstat file type" 4
field 15 "the file's fdstat flags" 1
field 20 "the file's filestat file type" 4
field 22 "the file's filestat size" 4294967301
od -An -v -t x1 -j 144 -N 64 "$out/records.stdout" > "$out/records.descriptor"
od -An -v -t x1 -j 208 -N 64 "$out/records.stdout" > "$out/records.path"
cmp -s "$out/records.descriptor" "$out/records.path" ||
  fail records "the file's filestat differs through the descriptor and through the path"
cases=$((cases + 1))

printf 'flat call example Wasmtime cases passed: %s\n' "$cases"
