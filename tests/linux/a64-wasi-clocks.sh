#!/usr/bin/env bash
# The stubs of clock_time_get and random_get of the AArch64 back end's WASI executables on requests
# at their edges, on an AArch64 Linux host.  For each case the script writes a module in WAT that
# imports the stream functions, clock_time_get, and random_get, makes one call, and writes the
# call's errno and the bytes around the call's region to standard output, as
# tests/linux/a64-wasi-clocks.py describes.  `a64-wasi module` writes the module's executable with
# the generator of the WASI executables, and the script runs the module in the repository's
# Wasmtime host and the executable on the host's processor and under qemu-aarch64, QEMU's user-mode
# emulator, each run within TIMEOUT seconds, 120 unless set, in a scope of one core and 2G of
# memory, 5G for the case of 2 GiB.  Each run must end with the outcome of the case's table:
# status 0 with the errno of the table, the shim's trap with status 2, or, in the Wasmtime host, a
# host function's error with status 1, and the checker must accept each output of status 0.  Each
# executable runs once more natively under strace, with the status of its other runs, and the
# checker requires the calls of the case and no other: for clocks 0 and 1, one `clock_gettime` of
# the clock into the shim's timespec; for a random buffer of at least one byte, a `getrandom` of the
# buffer with flags 0 and, after each short count, of the rest; and none for a trap or another case.
#
# The table states the Wasmtime host's outcomes as Wasmtime 44 gives them.  They differ from the
# executable's only for requests outside the WASI contract, where the shim's specification chose
# otherwise, and for the case of 2 GiB, which Wasmtime refuses: a clock of 4 or more, a time's
# pointer beyond the memory, or a random buffer beyond it is the shim's trap and a host function's
# error in Wasmtime; a pointer beyond the memory for clock 2 is the shim's trap and errno 8 in
# Wasmtime; a time's pointer that is not a multiple of 8 gets the time from the shim and an error
# from Wasmtime; random_get of no byte past the memory's end is the shim's trap and errno 0 in
# Wasmtime; and random_get of more than 2^26 bytes fills the buffer in the shim and is an error in
# Wasmtime, whose get-random-bytes takes at most 67,108,864 bytes.  The case of 2 GiB must make at
# least two calls of getrandom, since Linux returns fewer bytes than the first asks for.  The
# products lie in OUT, build/linux/a64-wasi-clocks unless set.
# Usage: tests/linux/a64-wasi-clocks.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/linux/a64-wasi-clocks}")
qemu=${QEMU_USER:-/usr/bin/qemu-aarch64}
host=$root/build/tools/leanexe-wasmtime-host
for tool in "$host" "$qemu"; do
  [ -x "$tool" ] || { echo "fail: $tool is missing"; exit 1; }
done
for tool in wasm-tools strace uv; do
  command -v "$tool" > /dev/null || { echo "fail: $tool is not on the search path"; exit 1; }
done
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build a64-wasi
# name kind pages A B executable Wasmtime
cases="c0 clock 1 0 4096 0 0
c1 clock 1 1 4096 0 0
c2 clock 1 2 4096 8 8
c3 clock 1 3 4096 8 8
c4 clock 1 4 4096 trap error
cmax clock 1 4294967295 4096 trap error
c0u clock 1 0 4099 0 error
c1u clock 1 1 4101 0 error
c0end clock 1 0 65528 0 0
c0over clock 1 0 65529 trap error
c0huge clock 1 0 4294967288 trap error
c2over clock 1 2 65529 trap 8
c4end clock 1 4 65528 trap error
r0 random 1 4096 0 0 0
r1 random 1 4096 1 0 0
r4096 random 1 4096 4096 0 0
r4097 random 1 4096 4097 0 0
r1m random 20 4096 1048576 0 0
r64m random 1100 4096 67108864 0 0
rend random 1 61439 4097 0 0
rover random 1 61440 4097 trap error
rsize0 random 1 65536 0 0 0
rpast0 random 1 65537 0 trap 0
rhuge random 1 4294967295 1 trap error
rbig random 1 4096 4294967295 trap error
runal random 1 4099 4097 0 0
r2g random 32770 4096 2147491840 0 error"

# wat KIND PAGES A B: the case module's text.
wat() {
  local kind=$1 pages=$2 size=$(($2 * 65536)) lo hi ptr n after head tail x
  # region LO HI: the call that writes the bytes from LO to HI when they lie in memory.
  region() {
    if [ "$1" -lt "$2" ] && [ "$2" -le "$size" ]; then
      echo "    (call \$out (i32.const $1) (i32.const $(($2 - $1))))"
    fi
  }
  cat <<EOF
(module
  (import "wasi_snapshot_preview1" "fd_read" (func \$fd_read (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "fd_write"
    (func \$fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func \$proc_exit (param i32)))
  (import "wasi_snapshot_preview1" "clock_time_get" (func \$clock (param i32 i64 i32) (result i32)))
  (import "wasi_snapshot_preview1" "random_get" (func \$random (param i32 i32) (result i32)))
  (memory (export "memory") $pages)
  (func \$out (param \$p i32) (param \$n i32)
    (i32.store (i32.const 0) (local.get \$p))
    (i32.store (i32.const 4) (local.get \$n))
    (i32.store (i32.const 12)
      (call \$fd_write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8))))
  (func (export "_start")
EOF
  if [ "$kind" = clock ]; then
    ptr=$4
    lo=$ptr
    [ "$ptr" -ge 32 ] && lo=$((ptr - 8))
    hi=$((ptr + 16))
    [ "$hi" -le "$size" ] || hi=$((ptr + 8))
    if [ "$hi" -le "$size" ]; then
      for ((x = lo; x < hi; x += 8)); do
        echo "    (i64.store (i32.const $x) (i64.const 0x1111111111111111))"
      done
    fi
    echo "    (i64.store (i32.const 16) (i64.extend_i32_u"
    echo "      (call \$clock (i32.const $3) (i64.const 0) (i32.const $ptr))))"
    echo "    (call \$out (i32.const 16) (i32.const 8))"
    region "$lo" "$hi"
  else
    ptr=$3 n=$4 after=$(($3 + $4))
    if [ "$ptr" -ge 32 ] && [ "$ptr" -le "$size" ]; then
      echo "    (i32.store8 (i32.const $((ptr - 1))) (i32.const 0x5A))"
    fi
    if [ "$after" -lt "$size" ]; then
      echo "    (i32.store8 (i32.const $after) (i32.const 0xA5))"
    fi
    echo "    (i64.store (i32.const 16) (i64.extend_i32_u"
    echo "      (call \$random (i32.const $ptr) (i32.const $n))))"
    echo "    (call \$out (i32.const 16) (i32.const 8))"
    head=$((n < 4096 ? n : 4096))
    if [ "$ptr" -ge 32 ]; then region $((ptr - 1)) $((ptr + head))
    else region "$ptr" $((ptr + head)); fi
    if [ "$n" -gt 4096 ]; then
      tail=$((n - 4096 < 4096 ? n - 4096 : 4096))
      region $((after - tail)) "$after"
    fi
    region "$after" $((after + 1))
  fi
  echo "  ))"
}

status=0
modules=()
while read -r name kind pages a b _ _; do
  wat "$kind" "$pages" "$a" "$b" > "$out/$name.wat"
  wasm-tools parse "$out/$name.wat" -o "$out/$name.wasm"
  modules+=("$out/$name.wasm" "$out/$name.elf" "$pages")
done <<< "$cases"
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-wasi module "${modules[@]}" ||
  { echo "fail: a64-wasi module"; exit 1; }
now=$(date +%s)
# scoped MEM COMMAND...: runs the command in a scope of one core and MEM of memory.
scoped() {
  local mem=$1
  shift
  systemd-run --user --scope -q -p CPUQuota=100% -p MemoryMax="$mem" timeout "${TIMEOUT:-120}" "$@"
}
# outcome NAME HOW CODE WANT KIND PAGES A B: checks the run's outcome and output.
outcome() {
  local got
  if [ "$3" -eq 0 ]; then
    if got=$(uv run tests/linux/a64-wasi-clocks.py "$5" "$6" "$7" "$8" "$out/$1.$2" "$now"); then
      got=${got#errno }
    else
      echo "fail: $1 $2: $got"
      status=1
      return
    fi
  elif [ "$3" -eq 2 ]; then got=trap
  elif [ "$3" -eq 1 ]; then got=error
  else got="status $3"; fi
  if [ "$got" = "$4" ]; then
    echo "pass: $1 $2: $got"
  else
    echo "fail: $1 $2: $got where $4 is due"
    status=1
  fi
}
while read -r name kind pages a b want wantw; do
  chmod +x "$out/$name.elf"
  mem=2G
  [ "$pages" -le 2000 ] || mem=5G
  code=0
  scoped "$mem" "$host" --stdout-file "$out/$name.wasmtime" --control-file "$out/$name.control" \
    run "$out/$name.wasm" 2> "$out/$name.wasmtime.err" || code=$?
  outcome "$name" wasmtime "$code" "$wantw" "$kind" "$pages" "$a" "$b"
  for how in native qemu; do
    if [ "$how" = native ]; then set -- "$out/$name.elf"; else set -- "$qemu" "$out/$name.elf"; fi
    code=0
    scoped "$mem" "$@" > "$out/$name.$how" 2> "$out/$name.$how.err" || code=$?
    outcome "$name" "$how" "$code" "$want" "$kind" "$pages" "$a" "$b"
  done
  wantc=0
  if [ "$want" = trap ]; then wantc=2; set --
  elif [ "$kind" = clock ] && [ "$a" -lt 2 ]; then set -- clock "$a"
  elif [ "$kind" = random ] && [ "$b" -gt 0 ]; then set -- random "$a" "$b"
  else set --; fi
  got=
  code=0
  scoped "$mem" strace -X raw -e trace=clock_gettime,getrandom -e raw=clock_gettime,getrandom \
    -o "$out/$name.strace" "$out/$name.elf" > /dev/null || code=$?
  if [ "$code" -eq "$wantc" ] && got=$(uv run tests/linux/a64-wasi-clocks.py calls \
      "$out/$name.elf" "$out/$name.strace" "$pages" "$@") &&
      { [ "$name" != r2g ] || [ "${got%% *}" -ge 2 ]; }
  then
    echo "pass: $name under strace: $got"
  else
    echo "fail: $name under strace: status $code, $got"
    status=1
  fi
done <<< "$cases"
exit "$status"
