#!/usr/bin/env bash
# The WASI commands of the AArch64 back end as Linux executables on an AArch64 Linux host: the
# readAll command of Verified/Examples/WasiReadAll.lean, which copies standard input to standard
# output and exits with status 1 once it has read more than 1,000,000 bytes.  a64-wasi emit writes
# readall.elf, and Lean elaborates tests/TestSupport/A64/ImageFilesWasiElf.lean in the directory of
# the file, so that the kernel checks that readall.elf holds the bytes that its generator gives and
# proves its theorems, each with no axiom beyond propext, Classical.choice, and Quot.sound.  The
# script also writes the command's module, readall.wasm, and runs it in the repository's Wasmtime
# host, build/tools/leanexe-wasmtime-host, on the inputs from files.  It runs the executable on
# the host's processor and under qemu-aarch64, QEMU's user-mode emulator, each run within TIMEOUT
# seconds, 120 unless set, in a scope of one core and 2G of memory.  Inputs of 0, 1, 4,095, 4,096,
# 4,097, 65,536, 1,000,000, 1,000,001, and 3,000,000 random bytes run from a file, where the
# executable's status and output must equal the Wasmtime host's, and from a pipe into which the
# script writes the input in pieces of 1, 3, 5, and 7 bytes, each after a pause of PAUSE seconds,
# 0.2 unless set, and then the rest.  An input of at most 1,000,000 bytes must give the input and
# status 0, and a longer one a prefix of more than 1,000,000 bytes and at most 4,096 more, with
# status 1.  Standard input a directory must give status 31, `isdir`, with nothing written, as in
# the Wasmtime host, and standard output /dev/full status 51, `nospc`, as in the Wasmtime host.
# Standard input closed gives status 8, `badf`, with nothing written, and standard output closed
# status 8.
#
# The script also emits environ.elf, the environment command of
# Verified/Examples/WasiSysEnviron.lean, whose stubs of environ_sizes_get and environ_get read
# Linux's initial stack, and Lean elaborates tests/TestSupport/A64/ImageFilesWasiEnviron.lean
# beside it, and args.elf, the command of tests/TestSupport/A64/WasiArgs.lean, which writes its
# arguments through args_sizes_get and args_get.  Each writes the count and the size that its call
# reports as 8 little-endian bytes each and then the strings, each followed by a zero byte.  The
# environment runs under env -i with no variable, two, empty values, 3,000 variables, and eight
# values of 120,000 bytes, and the arguments with argv[0] alone, an empty argv[0], empty arguments
# among others, 3,000 arguments, and eight arguments of 120,000 bytes, natively and under QEMU,
# each against the Wasmtime host with --env or --arg and against the bytes that the script
# computes.  Bytes outside UTF-8 run natively and under QEMU against the computed bytes alone, and
# through tests/linux/execve.py natively, an environment with empty strings, a string without '=',
# and a repeated name, and an empty argv, for which Linux gives argv[0] as an empty string: QEMU's
# user mode rebuilds the guest's environment and drops such entries.  strace must show that
# environ.elf and args.elf make no call but write and exit_group.
#
# The script also emits clockrandom.elf, the command of Verified/Examples/WasiClockRandom.lean,
# which reads three clocks and two buffers of random bytes through the stubs of clock_time_get and
# random_get, and Lean elaborates tests/TestSupport/A64/ImageFilesWasiClockElf.lean beside it.
# Four runs each in the Wasmtime host, on the host's processor, and under qemu-aarch64 must exit
# with status 0 and write what tests/linux/a64-wasi-clocks.py accepts: errnos 0, 0, 8, 0, and 0,
# readings of realtime within a day of the clock and of the first run, monotonic readings below
# 10^17, 5,000 random bytes with few zeros, and 16 random bytes that differ between runs.  A native
# run under strace must make `clock_gettime` of clocks 0 and 1 into the shim's timespec and then
# `getrandom` of 16 and of 5,000 bytes of linear memory with flags 0, and no other call but write
# and exit_group.  The products lie in OUT, build/linux/a64-wasi unless set.
# Usage: tests/linux/a64-wasi.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/linux/a64-wasi}")
qemu=${QEMU_USER:-/usr/bin/qemu-aarch64}
host=$root/build/tools/leanexe-wasmtime-host
limit=1000000
if [ ! -x "$host" ]; then
  echo "fail: the Wasmtime host $host is missing"
  exit 1
fi
for tool in strace uv; do
  command -v "$tool" > /dev/null || { echo "fail: $tool is not on the search path"; exit 1; }
done
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build a64-wasi \
  TestSupport.A64.WasiElf Verified.Examples.WasiReadAllNative \
  Verified.Examples.WasiSysEnvironNative Verified.Examples.WasiClockRandomNative LeanExe.A64.File
status=0
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-wasi emit "$out" || status=1
chmod +x "$out/readall.elf" "$out/environ.elf" "$out/args.elf" "$out/clockrandom.elf"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiReadAll \
  Verified.Examples.WasiReadAll.command.module "$out/readall.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiSysEnviron \
  Verified.Examples.WasiSysEnviron.command.module "$out/environ.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean TestSupport.A64.WasiArgs \
  TestSupport.A64.WasiArgs.command.module "$out/args.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiClockRandom \
  Verified.Examples.WasiClockRandom.command.module "$out/clockrandom.wasm"
# Elaborates the module $1 of tests/TestSupport/A64 in the directory of the files and requires $2
# reports of axioms, each a subset of the standard three.  Lean breaks a report longer than its
# format's width of 120 columns into lines, which the check joins.
kernel_check() {
  if tools/leanrun --timeout 60m --memory-high 12G lake env sh -c 'cd "$1" && lean "$2"' sh \
      "$out" "$root/tests/TestSupport/A64/$1.lean" >"$out/$1.check" 2>&1 &&
      sed -e ':a' -e '/depends on axioms: \[[^]]*$/{N;s/\n//;ba' -e '}' "$out/$1.check" \
        >"$out/$1.axioms" &&
      [ "$(grep -c "depends on axioms\|does not depend on any axioms" "$out/$1.axioms")" = "$2" ] &&
      ! grep "depends on axioms" "$out/$1.axioms" |
        sed 's/.*depends on axioms: \[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
        grep -qvx 'propext\|Classical.choice\|Quot.sound'; then
    echo "pass: the kernel's check of $1.lean"
  else
    echo "fail: the kernel's check of $1.lean: $(head -c 600 "$out/$1.check")"
    status=1
  fi
}
kernel_check ImageFilesWasiElf 6
kernel_check ImageFilesWasiEnviron 6
kernel_check ImageFilesWasiClockElf 6
# Runs the command given as arguments in a scope of one core and 2G of memory.
scoped() {
  systemd-run --user --scope -q -p CPUQuota=100% -p MemoryMax=2G timeout "${TIMEOUT:-120}" "$@"
}
# Writes the bytes of the file $1 in pieces of 1, 3, 5, and 7 bytes, each after a pause, and then
# the rest.
pieces() {
  local n off=0 size
  size=$(stat -c %s "$1")
  for n in 1 3 5 7; do
    [ "$off" -lt "$size" ] || return 0
    sleep "${PAUSE:-0.2}"
    dd if="$1" bs=1 skip="$off" count="$n" status=none
    off=$((off + n))
  done
  [ "$off" -lt "$size" ] || return 0
  sleep "${PAUSE:-0.2}"
  tail -c +"$((off + 1))" "$1"
}
# Checks the run named $1 of the input $2 that ended with status $3 and wrote the file $4: the
# input and status 0 for an input of at most `limit` bytes, and otherwise status 1 and a prefix of
# the input of more than `limit` bytes and at most 4,096 more.
check() {
  local size written
  size=$(stat -c %s "$2")
  written=$(stat -c %s "$4")
  if [ "$size" -le "$limit" ]; then
    if [ "$3" -eq 0 ] && cmp -s "$2" "$4"; then
      echo "pass: $1: status 0, $written bytes"
      return 0
    fi
  elif [ "$3" -eq 1 ] && [ "$written" -gt "$limit" ] && [ "$written" -le $((limit + 4096)) ] &&
      head -c "$written" "$2" | cmp -s - "$4"; then
    echo "pass: $1: status 1, $written bytes"
    return 0
  fi
  echo "fail: $1: status $3, $written bytes"
  status=1
}
# Checks the run named $1 that ended with status $2 and wrote the file $3 against the status $4
# and the file $5.
same() {
  if [ "$2" -eq "$4" ] && cmp -s "$5" "$3"; then
    echo "pass: $1: status $2 and $(stat -c %s "$3") bytes, as the Wasmtime host gives"
  else
    echo "fail: $1: status $2 where the Wasmtime host gives $4, or the output differs"
    status=1
  fi
}
for size in 0 1 4095 4096 4097 65536 $limit $((limit + 1)) $((3 * limit)); do
  in=$out/input-$size
  head -c "$size" /dev/urandom >"$in"
  code=0
  timeout "${TIMEOUT:-120}" "$host" --stdin-file "$in" --stdout-file "$out/wasmtime-$size.out" \
    --control-file "$out/wasmtime-$size.control" run "$out/readall.wasm" \
    2>"$out/wasmtime-$size.err" || code=$?
  check "$size bytes in the Wasmtime host from a file" "$in" "$code" "$out/wasmtime-$size.out"
  want=$code
  for how in native qemu; do
    if [ "$how" = native ]; then set -- "$out/readall.elf"
    else set -- "$qemu" "$out/readall.elf"; fi
    code=0
    scoped "$@" <"$in" >"$out/$how-$size.file" || code=$?
    check "$size bytes $how from a file" "$in" "$code" "$out/$how-$size.file"
    same "$size bytes $how from a file" "$code" "$out/$how-$size.file" "$want" \
      "$out/wasmtime-$size.out"
    code=0
    pieces "$in" | scoped "$@" >"$out/$how-$size.pipe" || code=$?
    check "$size bytes $how from a pipe in pieces" "$in" "$code" "$out/$how-$size.pipe"
  done
done
# Checks the run named $1 that ended with status $2 against the status $3, and when $4 names the
# file of the run's standard output, that the run wrote nothing to it.
fails() {
  if [ "$2" -eq "$3" ] && { [ -z "${4:-}" ] || [ ! -s "$4" ]; }; then
    echo "pass: $1: status $2${4:+, nothing written}"
  else
    echo "fail: $1: status $2 where $3 is due${4:+, $(stat -c %s "$4") bytes written}"
    status=1
  fi
}
code=0
timeout "${TIMEOUT:-120}" "$host" --stdin-file / --stdout-file "$out/wasmtime-dir.out" \
  --control-file "$out/wasmtime-dir.control" run "$out/readall.wasm" \
  2>"$out/wasmtime-dir.err" || code=$?
fails "standard input a directory in the Wasmtime host" "$code" 31 "$out/wasmtime-dir.out"
code=0
timeout "${TIMEOUT:-120}" "$host" --stdin-file "$out/input-4097" --stdout-file /dev/full \
  --control-file "$out/wasmtime-full.control" run "$out/readall.wasm" \
  2>"$out/wasmtime-full.err" || code=$?
fails "standard output /dev/full in the Wasmtime host" "$code" 51
for how in native qemu; do
  if [ "$how" = native ]; then set -- "$out/readall.elf"
  else set -- "$qemu" "$out/readall.elf"; fi
  code=0
  scoped "$@" <"$out" >"$out/$how-dir.out" || code=$?
  fails "standard input a directory $how" "$code" 31 "$out/$how-dir.out"
  code=0
  scoped "$@" <"$out/input-4097" >/dev/full || code=$?
  fails "standard output /dev/full $how" "$code" 51
  code=0
  scoped "$@" <&- >"$out/$how-closed-in.out" || code=$?
  fails "standard input closed $how" "$code" 8 "$out/$how-closed-in.out"
  code=0
  scoped "$@" <"$out/input-4097" >&- || code=$?
  fails "standard output closed $how" "$code" 8
done
# Writes the eight little-endian bytes of the number $1.
le64() {
  local i out=
  for i in 0 1 2 3 4 5 6 7; do out+=$(printf '\\%03o' $((($1 >> (8 * i)) & 255))); done
  printf "$out"
}
# Writes to the file $1 what the commands write for the strings $2 and after: their count and
# their size, each string with a zero byte, as 8 little-endian bytes each, and then the strings,
# each followed by a zero byte.
expect() {
  local f=$1 size=0 s
  shift
  for s in "$@"; do size=$((size + $(printf '%s' "$s" | wc -c) + 1)); done
  { le64 "$#"; le64 "$size"; for s in "$@"; do printf '%s\0' "$s"; done; } >"$f"
}
# Checks the run named $1 that ended with status $2 and wrote the file $3 against status 0 and the
# file $4.
expected() {
  if [ "$2" -eq 0 ] && cmp -s "$4" "$3"; then
    echo "pass: $1: status 0 and $(stat -c %s "$3") bytes, as expected"
  else
    echo "fail: $1: status $2, or the output differs from the expected bytes"
    status=1
  fi
}
# Runs the environment case $1 with the variables $2 and after: the Wasmtime host with --env,
# then environ.elf natively and under QEMU with env -i.
environ_case() {
  local name=$1 v code=0 c
  shift
  local hostargs=()
  for v in "$@"; do hostargs+=(--env "$v"); done
  expect "$out/environ-$name.want" "$@"
  timeout "${TIMEOUT:-120}" "$host" "${hostargs[@]}" --stdout-file "$out/environ-$name.host" \
    --control-file "$out/environ-$name.control" run "$out/environ.wasm" \
    2>"$out/environ-$name.err" || code=$?
  expected "environment $name in the Wasmtime host" "$code" "$out/environ-$name.host" \
    "$out/environ-$name.want"
  c=0
  scoped env -i "$@" "$out/environ.elf" >"$out/environ-$name.native" || c=$?
  same "environment $name native" "$c" "$out/environ-$name.native" "$code" \
    "$out/environ-$name.host"
  c=0
  scoped env -i "$@" "$qemu" "$out/environ.elf" >"$out/environ-$name.qemu" || c=$?
  same "environment $name under QEMU" "$c" "$out/environ-$name.qemu" "$code" \
    "$out/environ-$name.host"
}
# Runs the arguments case $1 with argv[0] $2 and the arguments $3 and after: the Wasmtime host
# with --arg, then args.elf natively with exec -a and under QEMU with -0.
args_case() {
  local name=$1 v code=0 c
  shift
  local hostargs=()
  for v in "$@"; do hostargs+=(--arg "$v"); done
  expect "$out/args-$name.want" "$@"
  timeout "${TIMEOUT:-120}" "$host" "${hostargs[@]}" --stdout-file "$out/args-$name.host" \
    --control-file "$out/args-$name.control" run "$out/args.wasm" \
    2>"$out/args-$name.err" || code=$?
  expected "arguments $name in the Wasmtime host" "$code" "$out/args-$name.host" \
    "$out/args-$name.want"
  c=0
  scoped bash -c 'a0=$1; shift; exec -a "$a0" "$@"' bash "$1" "$out/args.elf" "${@:2}" \
    >"$out/args-$name.native" || c=$?
  same "arguments $name native" "$c" "$out/args-$name.native" "$code" "$out/args-$name.host"
  c=0
  scoped "$qemu" -0 "$1" "$out/args.elf" "${@:2}" >"$out/args-$name.qemu" || c=$?
  same "arguments $name under QEMU" "$c" "$out/args-$name.qemu" "$code" "$out/args-$name.host"
}
environ_case none
environ_case two A=1 B=hello
environ_case empty E= F== G=a=b
many=()
for i in $(seq 1 3000); do many+=("V$i=value$i"); done
environ_case many "${many[@]}"
long=()
for i in 1 2 3 4 5 6 7 8; do long+=("L$i=$(head -c 120000 /dev/zero | tr '\0' "$i")"); done
environ_case long "${long[@]}"
bytes=("$(printf 'X=\377\376\200')" "$(printf '\303(=\342\202')")
expect "$out/environ-bytes.want" "${bytes[@]}"
c=0
scoped env -i "${bytes[@]}" "$out/environ.elf" >"$out/environ-bytes.native" || c=$?
expected "environment outside UTF-8 native" "$c" "$out/environ-bytes.native" \
  "$out/environ-bytes.want"
c=0
scoped env -i "${bytes[@]}" "$qemu" "$out/environ.elf" >"$out/environ-bytes.qemu" || c=$?
expected "environment outside UTF-8 under QEMU" "$c" "$out/environ-bytes.qemu" \
  "$out/environ-bytes.want"
expect "$out/environ-raw.want" "" NOEQUALS "" A=1 "" A=1
c=0
scoped uv run tests/linux/execve.py "$out/environ.elf" environ -- "" NOEQUALS "" A=1 "" A=1 \
  >"$out/environ-raw.native" || c=$?
expected "environment of empty strings, no '=', and a repeated name, native" "$c" \
  "$out/environ-raw.native" "$out/environ-raw.want"
args_case argv0 prog
args_case empty ''
args_case blanks prog '' a '' ''
many=()
for i in $(seq 1 3000); do many+=("arg$i"); done
args_case many prog "${many[@]}"
args_case long prog "${long[@]#L?=}"
expect "$out/args-none.want" ""
c=0
scoped uv run tests/linux/execve.py "$out/args.elf" -- >"$out/args-none.native" || c=$?
expected "no argument native, argv[0] empty" "$c" "$out/args-none.native" "$out/args-none.want"
# Checks that the trace of strace in the file $2 of the run named $1 holds no call but those of
# the sorted list $3, exit_group and write unless given, after the execve of the executable.
only_calls() {
  local calls want=${3:-exit_group write}
  calls=$(sed -n '/execve(/,$p' "$2" | tail -n +2 | sed 's/^[0-9]* *//; /^+++/d; s/(.*//' |
    sort -u | tr '\n' ' ')
  if [ "$calls" = "$want " ]; then
    echo "pass: $1 makes no call but $want"
  else
    echo "fail: $1 makes the calls $calls"
    status=1
  fi
}
env -i A=1 B=2 strace -f -X raw -o "$out/environ.strace" "$out/environ.elf" >/dev/null
only_calls environ.elf "$out/environ.strace"
strace -f -X raw -o "$out/args.strace" "$out/args.elf" x y >/dev/null
only_calls args.elf "$out/args.strace"
# The clock and random command.
now=$(date +%s)
for i in 1 2 3 4; do
  code=0
  timeout "${TIMEOUT:-120}" "$host" --stdout-file "$out/wasmtime-clock-$i.out" \
    --control-file "$out/wasmtime-clock-$i.control" run "$out/clockrandom.wasm" \
    2>"$out/wasmtime-clock-$i.err" || code=$?
  fails "clockrandom run $i in the Wasmtime host" "$code" 0
  for how in native qemu; do
    if [ "$how" = native ]; then set -- "$out/clockrandom.elf"
    else set -- "$qemu" "$out/clockrandom.elf"; fi
    code=0
    scoped "$@" >"$out/$how-clock-$i.out" || code=$?
    fails "clockrandom run $i $how" "$code" 0
  done
done
for how in wasmtime native qemu; do
  if got=$(uv run tests/linux/a64-wasi-clocks.py example "$now" "$out/$how-clock-1.out" \
      "$out/$how-clock-2.out" "$out/$how-clock-3.out" "$out/$how-clock-4.out"); then
    echo "pass: clockrandom's output $how"
  else
    echo "fail: clockrandom's output $how: $got"
    status=1
  fi
done
code=0
got=
scoped strace -X raw -e raw=clock_gettime,getrandom -o "$out/clockrandom.strace" \
  "$out/clockrandom.elf" >/dev/null || code=$?
if [ "$code" -eq 0 ] && got=$(uv run tests/linux/a64-wasi-clocks.py calls "$out/clockrandom.elf" \
    "$out/clockrandom.strace" 4096 clock 0 clock 1 random - 16 random - 5000); then
  echo "pass: clockrandom's calls under strace: $got"
else
  echo "fail: clockrandom's calls under strace: status $code, $got"
  status=1
fi
only_calls clockrandom.elf "$out/clockrandom.strace" "clock_gettime exit_group getrandom write"
exit "$status"
