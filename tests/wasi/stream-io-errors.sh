#!/bin/sh
set -eu
set -f

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

if [ "$#" -ne 3 ]; then
  printf 'Usage: tests/wasi/stream-io-errors.sh NAME NATIVE WASM\n' >&2
  exit 2
fi
name=$1
native=$2
wasm=$3
host="$root/build/tools/leanexe-wasmtime-host"
out="$root/build/$name/io-errors"
mkdir -p "$out"
printf '1\n2\n' >"$out/input"

expect_status() {
  if [ "$3" -ne "$2" ]; then
    printf '%s: %s status %s, expected %s\n' "$name" "$1" "$3" "$2" >&2
    exit 1
  fi
}

# A directory as stdin makes the first read fail with EISDIR, which WASI reports as errno 31.
status=0
timeout 30s "$host" --stdin-file / --stdout-file "$out/read.stdout" \
  --control-file "$out/read.control" run "$wasm" 2>"$out/read.stderr" || status=$?
expect_status 'Wasm read error' 31 "$status"
printf 'wasi-exit 31\n' | cmp - "$out/read.control"
test ! -s "$out/read.stdout"
test ! -s "$out/read.stderr"

status=0
timeout 30s "$native" </ >"$out/native-read.stdout" 2>"$out/native-read.stderr" || status=$?
expect_status 'native read error' 1 "$status"
test ! -s "$out/native-read.stdout"
grep -q 'error code: 21' "$out/native-read.stderr"

if [ ! -e /dev/full ]; then
  printf '%s I/O errors: 2 cases passed; /dev/full is absent, so the 2 write cases did not run\n' \
    "$name"
  exit 0
fi

# Writes to /dev/full fail with ENOSPC, which WASI reports as errno 51.
status=0
timeout 30s "$host" --stdin-file "$out/input" --stdout-file /dev/full \
  --control-file "$out/write.control" run "$wasm" 2>"$out/write.stderr" || status=$?
expect_status 'Wasm write error' 51 "$status"
printf 'wasi-exit 51\n' | cmp - "$out/write.control"
test ! -s "$out/write.stderr"

status=0
timeout 30s "$native" <"$out/input" >/dev/full 2>"$out/native-write.stderr" || status=$?
expect_status 'native write error' 1 "$status"
grep -q 'error code: 28' "$out/native-write.stderr"
printf '%s I/O errors: 4 cases passed\n' "$name"
