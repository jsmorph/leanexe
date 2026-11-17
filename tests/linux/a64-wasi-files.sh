#!/usr/bin/env bash
# The WASI commands of the AArch64 back end that open, read, write, and close files under the
# preopened directory, as Linux executables on an AArch64 Linux host: the files command of
# Verified/Examples/WasiFiles.lean, which writes a file in one bracket of withOpen and reads it back
# in another, and the module that tests/linux/wasi/files-cases.py writes, whose scenarios exercise
# path_open, fd_close, and fd_read and fd_write on a handle.  a64-wasi emit writes files.elf,
# a64-wasi wasm writes cases.elf from the module's binary, and Lean elaborates
# tests/TestSupport/A64/ImageFilesWasiFiles.lean in the directory of the files, so that the kernel
# checks that files.elf holds the bytes that its generator gives and proves its theorems, each with
# no axiom beyond propext, Classical.choice, and Quot.sound.
#
# Each run takes a fresh directory with step 4's fixture: a file f, a directory sub with a file g,
# and symbolic links to f, to /etc/hostname, to .., to sub/.., to a missing name, and to sub.  The
# executable takes it as descriptor 3 and the repository's Wasmtime host, build/tools/
# leanexe-wasmtime-host or HOST, with --dir, each run within TIMEOUT seconds, 120 unless set.
# files.elf must give the Wasmtime host's output, status, and directory.  For the scenarios of the
# path cases, the flags, the closes, and the handles, every case's output must equal the Wasmtime
# host's but for the cases that tests/linux/wasi/files-expected.txt lists with the specification's
# reason, and the directories afterwards must agree.  The scenario of magic links runs with
# /proc/self as descriptor 3 and as the host's directory.
#
# QEMU 8.2.2 answers openat2 with ENOSYS, so each run under qemu-aarch64 must equal the native run
# with strace injecting ENOSYS into every openat2.  With 1,024 descriptors the opens without closes
# end with errno 29 after 1,020 opens, and with 2,048 the 1,021st open returns descriptor 1,024,
# which ends the run with the shim's trap, status 2.  Each request that the shim refuses with a
# trap ends the run with status 2 after the open that precedes it.  strace -X raw shows the open_how
# record of every openat2 of the flag scenario, which must hold the flags of openFlagsWord, the mode
# 0666 exactly for O_CREAT, and the resolution 0xa, and the raw arguments of each openat2 name
# descriptor 3, the path buffer and the record in the shim's scratch, and the size 24.  strace's
# fault injection makes openat2 return EAGAIN, after which the shim retries while fewer than four
# calls were made, and descriptor 1,024 or 4,096, which ends the run with status 2, and makes close
# fail with EIO, which gives errno 29, or return 5, which ends the run with status 2.  The products
# lie in OUT, build/linux/a64-wasi-files unless set.  With --runs DIR, the script builds and checks
# nothing and runs the executables and modules that an earlier run left in DIR, on a host that needs
# neither Lean nor wasm-tools.
# Usage: tests/linux/a64-wasi-files.sh [--runs DIR]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
qemu=${QEMU_USER:-/usr/bin/qemu-aarch64}
host=${HOST:-$root/build/tools/leanexe-wasmtime-host}
status=0
if [ "${1:-}" = --runs ] && [ -n "${2:-}" ]; then
  out=$(realpath "$2")
elif [ $# -eq 0 ]; then
  out=$(realpath -m "${OUT:-$root/build/linux/a64-wasi-files}")
  rm -rf "${out:?}"
  mkdir -p "$out"
  tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build a64-wasi \
    TestSupport.A64.WasiElf Verified.Examples.WasiFilesNative LeanExe.A64.File
  tools/leanrun --timeout 30m lake env .lake/build/bin/a64-wasi emit "$out" || status=1
  uv run tests/linux/wasi/files-cases.py "$out/cases.wat" "$out/cases.txt" "$out/flags.txt"
  wasm-tools parse "$out/cases.wat" -o "$out/cases.wasm"
  tools/leanrun --timeout 30m lake env .lake/build/bin/a64-wasi wasm "$out/cases.wasm" \
    "$out/cases.elf" || status=1
  tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiFiles \
    Verified.Examples.WasiFiles.command.module "$out/files.wasm"
  cp tests/linux/wasi/files-expected.txt tests/linux/wasi/files-compare.py \
    tests/linux/wasi/files-flags.py "$out/"
  if tools/leanrun --timeout 60m --memory-high "${CHECK_MEM:-20G}" lake env sh -c \
      'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/A64/ImageFilesWasiFiles.lean" \
      >"$out/check.log" 2>&1 &&
      [ "$(grep -c "depends on axioms\|does not depend on any axioms" "$out/check.log")" = 6 ] &&
      ! grep "depends on axioms" "$out/check.log" |
        sed 's/.*depends on axioms: \[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
        grep -qvx 'propext\|Classical.choice\|Quot.sound'; then
    echo "pass: the kernel's check of ImageFilesWasiFiles.lean"
  else
    echo "fail: the kernel's check of ImageFilesWasiFiles.lean: $(head -c 600 "$out/check.log")"
    status=1
  fi
else
  echo "usage: tests/linux/a64-wasi-files.sh [--runs DIR]" >&2
  exit 2
fi
if [ ! -x "$host" ]; then
  echo "fail: the Wasmtime host $host is missing"
  exit 1
fi
chmod +x "$out/files.elf" "$out/cases.elf"
runs=$out/runs
rm -rf "$runs"
mkdir -p "$runs"
# A fresh directory at $1 with the fixture of step 4's path probe.
fixture() {
  mkdir -p "$1/sub"
  printf abcd >"$1/f"
  printf xy >"$1/sub/g"
  ln -s f "$1/in"
  ln -s /etc/hostname "$1/out"
  ln -s .. "$1/up"
  ln -s sub/.. "$1/subup"
  ln -s nothere "$1/dangling"
  ln -s sub "$1/sublink"
}
# The names, kinds, sizes, link targets, modes, and contents of the directory $1.
listing() {
  (cd "$1" && find . -printf '%p %y %s %l %m\n' | LC_ALL=C sort &&
    find . -type f -print0 | LC_ALL=C sort -z | xargs -0 -r md5sum)
}
limited() {
  timeout "${TIMEOUT:-120}" "$@"
}
# Requires the run named $1 with status $2 to have status $3.
want_status() {
  if [ "$2" -eq "$3" ]; then
    echo "pass: $1: status $2"
  else
    echo "fail: $1: status $2 where $3 is due"
    status=1
  fi
}
# Requires the files $2 and $3 to be equal, for the check named $1.
same_file() {
  if cmp -s "$2" "$3"; then
    echo "pass: $1"
  else
    echo "fail: $1"
    status=1
  fi
}
# The files command: native and in the Wasmtime host.
fixture "$runs/n-files"
fixture "$runs/w-files"
code=0
limited "$out/files.elf" </dev/null >"$runs/n-files.out" 3<"$runs/n-files" || code=$?
want=0
limited "$host" --dir "$runs/w-files" --stdin-file /dev/null --stdout-file "$runs/w-files.out" \
  run "$out/files.wasm" 2>"$runs/w-files.err" || want=$?
want_status "files native against the Wasmtime host's status $want" "$code" "$want"
same_file "files native: the Wasmtime host's output" "$runs/n-files.out" "$runs/w-files.out"
listing "$runs/n-files" >"$runs/n-files.list"
listing "$runs/w-files" >"$runs/w-files.list"
same_file "files native: the Wasmtime host's directory" "$runs/n-files.list" "$runs/w-files.list"
# The scenarios of the cases module: native against the Wasmtime host, case by case.
for s in p f c h; do
  fixture "$runs/n-$s"
  fixture "$runs/w-$s"
  printf %s "$s" >"$runs/in-$s"
  code=0
  limited "$out/cases.elf" <"$runs/in-$s" >"$runs/n-$s.out" 3<"$runs/n-$s" || code=$?
  want_status "scenario $s native" "$code" 0
  code=0
  limited "$host" --dir "$runs/w-$s" --stdin-file "$runs/in-$s" --stdout-file "$runs/w-$s.out" \
    run "$out/cases.wasm" 2>"$runs/w-$s.err" || code=$?
  want_status "scenario $s in the Wasmtime host" "$code" 0
  uv run "$out/files-compare.py" "$out/cases.txt" "$out/files-expected.txt" "$s" \
    "scenario $s native against the Wasmtime host" "$runs/n-$s.out" "$runs/w-$s.out" ||
    status=1
  listing "$runs/n-$s" >"$runs/n-$s.list"
  listing "$runs/w-$s" >"$runs/w-$s.list"
  same_file "scenario $s: the Wasmtime host's directory" "$runs/n-$s.list" "$runs/w-$s.list"
done
printf m >"$runs/in-m"
code=0
limited "$out/cases.elf" <"$runs/in-m" >"$runs/n-m.out" 3</proc/self || code=$?
want_status "scenario m native" "$code" 0
code=0
limited "$host" --dir /proc/self --stdin-file "$runs/in-m" --stdout-file "$runs/w-m.out" \
  run "$out/cases.wasm" 2>"$runs/w-m.err" || code=$?
want_status "scenario m in the Wasmtime host" "$code" 0
uv run "$out/files-compare.py" "$out/cases.txt" "$out/files-expected.txt" m \
  "scenario m native against the Wasmtime host" "$runs/n-m.out" "$runs/w-m.out" || status=1
# Under QEMU against the native run with ENOSYS injected into every openat2.
for s in p f c h 1 2 3 4 5 6; do
  printf %s "$s" >"$runs/in-$s"
  fixture "$runs/q-$s"
  code=0
  limited "$qemu" "$out/cases.elf" <"$runs/in-$s" >"$runs/q-$s.out" 3<"$runs/q-$s" || code=$?
  fixture "$runs/e-$s"
  want=0
  limited strace -f -o "$runs/e-$s.log" -e trace=openat2 -e inject=openat2:error=ENOSYS \
    "$out/cases.elf" <"$runs/in-$s" >"$runs/e-$s.out" 3<"$runs/e-$s" || want=$?
  want_status "scenario $s under qemu against the native run with ENOSYS" "$code" "$want"
  same_file "scenario $s under qemu: the native run's output with ENOSYS" "$runs/q-$s.out" \
    "$runs/e-$s.out"
done
fixture "$runs/q-files"
code=0
limited "$qemu" "$out/files.elf" </dev/null >"$runs/q-files.out" 3<"$runs/q-files" || code=$?
want_status "files under qemu, openat2 failing with ENOSYS" "$code" 29
# The descriptor limit.
fixture "$runs/n-l"
printf l >"$runs/in-l"
code=0
(ulimit -n 1024 && limited "$out/cases.elf" <"$runs/in-l" >"$runs/n-l.out" 3<"$runs/n-l") ||
  code=$?
if [ "$code" -eq 0 ] && [ "$(stat -c %s "$runs/n-l.out")" -eq 2043 ] &&
    [ "$(tail -c 1 "$runs/n-l.out" | od -An -tu1 | tr -d ' ')" = 29 ]; then
  echo "pass: 1,024 descriptors: 1,020 opens and then errno 29"
else
  echo "fail: 1,024 descriptors: status $code, $(stat -c %s "$runs/n-l.out") bytes"
  status=1
fi
code=0
(ulimit -n 2048 && limited "$out/cases.elf" <"$runs/in-l" >"$runs/n-l2.out" 3<"$runs/n-l") ||
  code=$?
if [ "$code" -eq 2 ] && [ "$(stat -c %s "$runs/n-l2.out")" -eq 2042 ]; then
  echo "pass: 2,048 descriptors: 1,020 opens and then the shim's trap at descriptor 1,024"
else
  echo "fail: 2,048 descriptors: status $code, $(stat -c %s "$runs/n-l2.out") bytes"
  status=1
fi
# The requests that the shim refuses with a trap.
printf '\376\377\000\377' >"$runs/trap.want"
for k in 1 2 3 4 5 6; do
  fixture "$runs/n-$k"
  code=0
  limited "$out/cases.elf" <"$runs/in-$k" >"$runs/n-$k.out" 3<"$runs/n-$k" || code=$?
  want_status "trap $k native" "$code" 2
  same_file "trap $k native: the output before the trap" "$runs/n-$k.out" "$runs/trap.want"
done
# The open_how records and the arguments of openat2.
fixture "$runs/x-f"
limited strace -f -X raw -o "$runs/x-f.log" -e trace=openat2 "$out/cases.elf" <"$runs/in-f" \
  >"$runs/x-f.out" 3<"$runs/x-f"
uv run "$out/files-flags.py" "$out/flags.txt" "$runs/x-f.log" || status=1
area=$(od -An -tu8 -j 136 -N 8 "$out/cases.elf" | tr -d ' ')
scratch=$((area + 4096 + 4096 * 65536))
fixture "$runs/r-p"
limited strace -f -e raw=openat2 -o "$runs/r-p.log" -e trace=openat2 "$out/cases.elf" \
  <"$runs/in-p" >"$runs/r-p.out" 3<"$runs/r-p"
args=$(printf 'openat2(0x3, 0x%x, 0x%x, 0x18)' $((scratch + 1080)) $((scratch + 1056)))
if [ "$(grep -c 'openat2(' "$runs/r-p.log")" -gt 0 ] &&
    ! grep 'openat2(0x3,' "$runs/r-p.log" | grep -vqF "$args"; then
  echo "pass: every openat2 of descriptor 3 names the scratch's path buffer and record"
else
  echo "fail: the arguments of openat2: $(grep -m1 'openat2(' "$runs/r-p.log")"
  status=1
fi
# Faults that strace injects into the files command.
fault() {
  local name=$1 inject=$2 want=$3 calls=$4 code=0
  fixture "$runs/fault-$name"
  limited strace -f -o "$runs/fault-$name.log" -e trace=openat2,close -e inject="$inject" \
    "$out/files.elf" </dev/null >"$runs/fault-$name.out" 3<"$runs/fault-$name" || code=$?
  local made
  made=$(grep -c 'openat2(' "$runs/fault-$name.log" || true)
  if [ "$code" -eq "$want" ] && { [ -z "$calls" ] || [ "$made" -eq "$calls" ]; }; then
    echo "pass: files with $inject: status $code, $made openat2 calls"
  else
    echo "fail: files with $inject: status $code where $want is due, $made openat2 calls"
    status=1
  fi
}
fault again3 openat2:error=EAGAIN:when=1..3 0 5
fault again4 openat2:error=EAGAIN:when=1..4 29 4
fault again openat2:error=EAGAIN 29 4
fault d1024 openat2:retval=1024:when=1 2 1
fault d4096 openat2:retval=4096:when=1 2 1
fault eio close:error=EIO:when=2 29 ""
fault five close:retval=5:when=2 2 ""
exit "$status"
