#!/bin/sh
# Tests the flat WASI calls: checks the call descriptions against the pinned witx, runs the frame
# test module in the Wasmtime host with several argument lists, runs the frame test of every flat
# function with a fresh preopened directory and the frame tests with seeded faults, and checks that
# Wasmtime traps on a clock id outside the clock enum.  Usage: tests/wasi/sys-run.sh [WITX_DIR]
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
witx=$(CDPATH= cd -- "$witx" && pwd)
cd "$root"
out="$root/build/wasi/sys"
host="$root/build/tools/leanexe-wasmtime-host"
mkdir -p "$out"
if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi
if [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  printf 'Native host is older than tools/wasmtime-host.c; rebuild it with %s\n' \
    tools/build-wasmtime-host.sh >&2
  exit 1
fi

fail() {
  printf 'flat calls %s: %s\n' "$1" "$2" >&2
  exit 1
}

uv run tools/wasi-calls.py "$witx" > "$out/descriptions.txt" ||
  fail "descriptions" "$(cat "$out/descriptions.txt")"
uv run tests/wasi/witx-lowering.py "$witx" > "$out/lowering.txt" ||
  fail "independent lowering" "$(cat "$out/lowering.txt")"

# Seeded faults.  The generator's check runs in a copy of the generated files' directories, and
# alter NAME FILE EXPRESSION changes FILE of the copy with the sed EXPRESSION, expects the check to
# fail, and restores FILE.
copy="$out/generator"
rm -rf "$copy"
mkdir -p "$copy/LeanExe" "$copy/Verified" "$copy/tests/wasi"
cp -R LeanExe/Wasi "$copy/LeanExe/Wasi"
cp -R Verified/Wasi "$copy/Verified/Wasi"
cp -R tests/wasi/sys "$copy/tests/wasi/sys"
rejected=0
alter() {
  cp "$copy/$2" "$copy/$2.saved"
  sed -i "$3" "$copy/$2"
  cmp -s "$copy/$2" "$copy/$2.saved" && fail "seeded fault $1" "the expression changed nothing"
  if (cd "$copy" && uv run "$root/tools/wasi-calls.py" "$witx" > "$out/fault-$1.txt" 2>&1); then
    fail "seeded fault $1" "the generator's check passed"
  fi
  mv "$copy/$2.saved" "$copy/$2"
  rejected=$((rejected + 1))
}
(cd "$copy" && uv run "$root/tools/wasi-calls.py" "$witx" > "$out/fault-none.txt" 2>&1) ||
  fail "seeded faults" "the unaltered copy fails the generator's check"
alter enum LeanExe/Wasi/CallTable.lean '0,/\.enum32 4/s//.enum32 5/'
alter field LeanExe/Wasi/SysCalls.lean '0,/reply\.field 0 16 8/s//reply.field 0 12 8/'
alter frame tests/wasi/sys/frame-all.wat '0,/(i32\.const 0xA5)/s//(i32.const 0xA4)/'
alter stray LeanExe/Wasi/Sys.lean \
  '$a def strayClose : Call := { name := "fd_close", params := [.word64] }'
sed '0,/(2, 2), (8, 8), (16, 8)/s//(2, 2), (8, 8), (12, 8)/' LeanExe/Wasi/CallTable.lean \
  > "$out/layout-fault.lean"
if uv run tests/wasi/witx-lowering.py "$witx" "$out/layout-fault.lean" \
  > "$out/fault-layout.txt" 2>&1
then
  fail "seeded fault layout" "the independent lowering accepted an altered record layout"
fi
rejected=$((rejected + 1))
printf 'flat call seeded faults detected: %s\n' "$rejected"

wasm-tools parse tests/wasi/sys/frame.wat -o "$out/frame.wasm"
wasm-tools parse tests/wasi/sys/frame-all.wat -o "$out/frame-all.wasm"
wasm-tools parse tests/wasi/sys/clock-invalid.wat -o "$out/clock-invalid.wasm"
wasm-tools validate "$out/frame.wasm"
wasm-tools validate "$out/frame-all.wasm"
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

# The frame test of every flat function runs with a fresh directory preopened at descriptor 3.  Each
# seeded fault's frame test must exit with the status that tools/wasi-calls.py prints for it.
dir="$out/frame-dir"
rm -rf "$dir"
mkdir "$dir"
status=0
timeout 60s "$host" --dir "$dir" --arg prog --arg a run "$out/frame-all.wasm" \
  2> "$out/frame-all.stderr" || status=$?
[ "$status" -eq 0 ] || fail "frame of every function" "status $status"
cases=$((cases + 1))
faults="$out/frame-faults"
rm -rf "$faults"
uv run tools/wasi-calls.py --frame-faults "$faults" "$witx" > "$out/frame-faults.txt"
seeded=0
while read -r name expected; do
  wasm-tools parse "$faults/$name.wat" -o "$faults/$name.wasm"
  rm -rf "$dir"
  mkdir "$dir"
  status=0
  timeout 60s "$host" --dir "$dir" --arg prog --arg a run "$faults/$name.wasm" \
    < /dev/null 2> "$faults/$name.stderr" || status=$?
  [ "$status" -eq "$expected" ] ||
    fail "seeded frame fault $name" "status $status, expected $expected"
  if [ "$expected" -eq 1 ]; then
    grep -q 'Pointer not aligned' "$faults/$name.stderr" ||
      fail "seeded frame fault $name" "no alignment trap"
  fi
  seeded=$((seeded + 1))
done < "$out/frame-faults.txt"
[ "$seeded" -gt 0 ] || fail "seeded frame faults" "the generator wrote none"
printf 'frame test seeded faults detected: %s\n' "$seeded"

status=0
timeout 60s "$host" run "$out/clock-invalid.wasm" 2> "$out/clock-invalid.stderr" || status=$?
[ "$status" -eq 1 ] || fail "invalid clock" "status $status"
grep -q 'Invalid enum value Clockid' "$out/clock-invalid.stderr" ||
  fail "invalid clock" "no enum trap"
cases=$((cases + 1))

printf 'flat call Wasmtime cases passed: %s\n' "$cases"
