#!/bin/sh
# Builds the flat call example, checks its axioms, runs its native cases, and runs its module in
# the Wasmtime host with several argument lists.  Each run must exit with status 0 and write the
# arguments with a zero byte after each, the argument count and size as 8 little-endian bytes each,
# a nonzero clock reading, and 16 random bytes.
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

tools/leanrun --timeout 30m --log "$out/build.log" lake build Verified.Examples.WasiSys
tools/leanrun --timeout 5m lake env lean tests/wasi/SysAxioms.lean
tools/leanrun --timeout 5m lake env lean --run tests/wasi/SysExample.lean
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiSys \
  Verified.Examples.WasiSys.command.module "$module"
wasm-tools validate "$module"

fail() {
  printf 'flat call example %s: %s\n' "$1" "$2" >&2
  exit 1
}

# word FILE OFFSET: the unsigned little-endian 8-byte word at OFFSET.
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
  [ "$written" -eq $((size + 40)) ] || fail "$name" "wrote $written bytes"
  head -c "$size" "$stdout" | cmp -s - "$expected" || fail "$name" "wrong argument bytes"
  [ "$(word "$stdout" "$size")" = "$count" ] || fail "$name" "count $(word "$stdout" "$size")"
  [ "$(word "$stdout" $((size + 8)))" = "$size" ] || fail "$name" "size"
  [ "$(word "$stdout" $((size + 16)))" != 0 ] || fail "$name" "clock reading 0"
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
run one --arg prog
check one 1 "$out/one.expected"

printf 'prog\000a\000b c\000\000' > "$out/four.expected"
run four --arg prog --arg a --arg "b c" --arg ""
check four 4 "$out/four.expected"

long=$(head -c 4096 /dev/zero | tr '\0' x)
printf 'prog\000%s\000' "$long" > "$out/long.expected"
run long --arg prog --arg "$long"
check long 2 "$out/long.expected"

printf 'flat call example Wasmtime cases passed: %s\n' "$cases"
