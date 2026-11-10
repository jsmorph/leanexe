#!/bin/sh
# Builds the readAll example, runs its native cases, and runs its module in the Wasmtime host on
# inputs from files and from pipes, at the sizes around a read's capacity and around the limit,
# with a read error and a write error.
set -eu
set -f
if ! command -v wasm-tools > /dev/null 2>&1; then
  printf 'wasm-tools is not on the search path\n' >&2
  exit 1
fi

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
out="$root/build/wasi/readall"
host="$root/build/tools/leanexe-wasmtime-host"
module="$out/readall.wasm"
limit=1000000
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi

tools/leanrun --timeout 30m --log "$out/build.log" lake build Verified.Examples.WasiReadAll
tools/leanrun --timeout 5m lake env lean tests/wasi/ReadAllAxioms.lean
tools/leanrun --timeout 5m lake env lean --run tests/wasi/ReadAll.lean
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiReadAll \
  Verified.Examples.WasiReadAll.command.module "$module"
wasm-tools validate "$module"

cases=0

fail() {
  printf 'readAll %s: %s\n' "$1" "$2" >&2
  exit 1
}

# check NAME INPUT OUTPUT CONTROL CAPACITY: an input of at most `limit` bytes is copied whole with
# status 0, and a longer one gives a prefix of more than `limit` bytes and less than `limit` plus
# the host's largest reply, with status 1.
check() {
  name=$1 input=$2 output=$3 control=$4 largest=$5
  size=$(wc -c < "$input")
  written=$(wc -c < "$output")
  if [ "$size" -le "$limit" ]; then
    cmp "$input" "$output" || fail "$name" "output differs from input"
    printf 'wasi-exit 0\n' | cmp -s - "$control" || fail "$name" "control $(cat "$control")"
  else
    [ "$written" -gt "$limit" ] || fail "$name" "wrote $written bytes"
    [ "$written" -le $((limit + largest)) ] || fail "$name" "wrote $written bytes"
    head -c "$written" "$input" | cmp -s - "$output" || fail "$name" "output is no prefix"
    printf 'wasi-exit 1\n' | cmp -s - "$control" || fail "$name" "control $(cat "$control")"
  fi
  cases=$((cases + 1))
}

for size in 0 1 4095 4096 4097 65536 $limit $((limit + 1)) $((3 * limit)); do
  input="$out/input-$size"
  head -c "$size" /dev/urandom > "$input"
  status=0
  timeout 60s "$host" --stdin-file "$input" --stdout-file "$out/file-$size.stdout" \
    --control-file "$out/file-$size.control" run "$module" 2> "$out/file-$size.stderr" ||
    status=$?
  check "file of $size bytes" "$input" "$out/file-$size.stdout" "$out/file-$size.control" 4096
  status=0
  cat "$input" | timeout 60s "$host" --stdout-file "$out/pipe-$size.stdout" \
    --control-file "$out/pipe-$size.control" run "$module" 2> "$out/pipe-$size.stderr" ||
    status=$?
  check "pipe of $size bytes" "$input" "$out/pipe-$size.stdout" "$out/pipe-$size.control" 1024
done

# A directory as stdin makes the first read fail with EISDIR, which WASI reports as errno 31.
status=0
timeout 60s "$host" --stdin-file / --stdout-file "$out/read-error.stdout" \
  --control-file "$out/read-error.control" run "$module" 2> "$out/read-error.stderr" || status=$?
[ "$status" -eq 31 ] || fail "read error" "status $status"
printf 'wasi-exit 31\n' | cmp -s - "$out/read-error.control" || fail "read error" "control"
[ ! -s "$out/read-error.stdout" ] || fail "read error" "wrote bytes"
cases=$((cases + 1))

# Writes to /dev/full fail with ENOSPC, which WASI reports as errno 51.
if [ -e /dev/full ]; then
  status=0
  timeout 60s "$host" --stdin-file "$out/input-4097" --stdout-file /dev/full \
    --control-file "$out/write-error.control" run "$module" 2> "$out/write-error.stderr" ||
    status=$?
  [ "$status" -eq 51 ] || fail "write error" "status $status"
  printf 'wasi-exit 51\n' | cmp -s - "$out/write-error.control" || fail "write error" "control"
  cases=$((cases + 1))
fi

printf 'readAll Wasmtime cases passed: %s\n' "$cases"
