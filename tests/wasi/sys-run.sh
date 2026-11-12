#!/bin/sh
# Tests the flat WASI calls: checks the call descriptions against the pinned witx, runs the frame
# test module in the Wasmtime host with several argument lists, and checks that Wasmtime traps on a
# clock id outside the clock enum.  Usage: tests/wasi/sys-run.sh [WITX_DIR]
#
# WITX_DIR holds wasi_snapshot_preview1.witx and typenames.witx of WebAssembly/WASI commit
# fae981bae14809d91f9bc2d63852d461f331d161; the default is tests/wasi/witx.
set -eu
set -f
if [ "$#" -gt 1 ]; then
  printf 'Usage: %s [WITX_DIR]\n' "$0" >&2
  exit 2
fi
if ! command -v wasm-tools > /dev/null 2>&1; then
  printf 'wasm-tools is not on the search path\n' >&2
  exit 1
fi

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
witx=${1:-$root/tests/wasi/witx}
cd "$root"
out="$root/build/wasi/sys"
host="$root/build/tools/leanexe-wasmtime-host"
mkdir -p "$out"
if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi
if [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  printf 'Native host is older than tools/wasmtime-host.c; rebuild it with tools/build-wasmtime-host.sh\n' >&2
  exit 1
fi

fail() {
  printf 'flat calls %s: %s\n' "$1" "$2" >&2
  exit 1
}

uv run tools/wasi-calls.py "$witx" > "$out/descriptions.txt" || fail "descriptions" "$(cat "$out/descriptions.txt")"

# reject NAME EXPRESSION: the checker rejects the descriptions altered by the sed EXPRESSION.
rejected=0
reject() {
  sed "$2" LeanExe/Wasi/Calls.lean > "$out/calls-$1.lean"
  if uv run tools/wasi-calls.py "$witx" "$out/calls-$1.lean" > "$out/calls-$1.txt" 2>&1; then
    fail "descriptions" "the checker accepted the altered description $1"
  fi
  rejected=$((rejected + 1))
}
reject enum 's/\.enum32 4/.enum32 5/'
reject shown 's/\.reported 4 4 false/.reported 4 4 true/'
reject reporter 's/reporter := some "args_sizes_get"/reporter := some "environ_sizes_get"/'
reject form 's/^end Call$/def fdClose : Call := ⟨"fd_close", [.word64], none⟩\nend Call/'
printf 'flat call altered descriptions rejected: %s\n' "$rejected"

wasm-tools parse tests/wasi/sys/frame.wat -o "$out/frame.wasm"
wasm-tools parse tests/wasi/sys/clock-invalid.wat -o "$out/clock-invalid.wasm"
wasm-tools validate "$out/frame.wasm"
wasm-tools validate "$out/clock-invalid.wasm"

long=$(head -c 4096 /dev/zero | tr '\0' x)
cases=0
status=0
timeout 60s "$host" run "$out/frame.wasm" 2> "$out/frame-none.stderr" || status=$?
[ "$status" -eq 0 ] || fail "frame without arguments" "status $status"
cases=$((cases + 1))
status=0
timeout 60s "$host" --arg prog run "$out/frame.wasm" 2> "$out/frame-one.stderr" || status=$?
[ "$status" -eq 0 ] || fail "frame with one argument" "status $status"
cases=$((cases + 1))
status=0
timeout 60s "$host" --arg prog --arg a --arg "b c" --arg "" run "$out/frame.wasm" \
  2> "$out/frame-four.stderr" || status=$?
[ "$status" -eq 0 ] || fail "frame with four arguments" "status $status"
cases=$((cases + 1))
status=0
timeout 60s "$host" --arg prog --arg "$long" run "$out/frame.wasm" 2> "$out/frame-long.stderr" ||
  status=$?
[ "$status" -eq 0 ] || fail "frame with a 4096-byte argument" "status $status"
cases=$((cases + 1))

status=0
timeout 60s "$host" run "$out/clock-invalid.wasm" 2> "$out/clock-invalid.stderr" || status=$?
[ "$status" -eq 1 ] || fail "invalid clock" "status $status"
grep -q 'Invalid enum value Clockid' "$out/clock-invalid.stderr" || fail "invalid clock" "no enum trap"
cases=$((cases + 1))

printf 'flat call Wasmtime cases passed: %s\n' "$cases"
