#!/usr/bin/env bash
# The WASI commands of the AArch64 back end that read the preopened directory, as Linux executables
# on an AArch64 Linux host: the prestat command of Verified/Examples/WasiPrestat.lean, which writes
# what fd_prestat_get and fd_prestat_dir_name answer for descriptor 3, and the module of
# tests/linux/wasi/prestat-numbers.wat, which writes their answers for the descriptor numbers 0 to
# 5, 1023, 1024, 2^31 - 1, 2^31, and 2^32 - 1.  a64-wasi emit writes prestat.elf, a64-wasi wasm
# writes numbers.elf from the module's binary, and Lean elaborates
# tests/TestSupport/A64/ImageFilesWasiPrestat.lean in the directory of the files, so that the
# kernel checks that prestat.elf holds the bytes that its generator gives and proves its theorems,
# each with no axiom beyond propext, Classical.choice, and Quot.sound.
#
# Each executable runs on the host's processor and under qemu-aarch64, QEMU's user-mode emulator,
# and its module in the repository's Wasmtime host, build/tools/leanexe-wasmtime-host or HOST, each
# run within TIMEOUT seconds, 60 unless set.  With descriptor 3 a directory, which the Wasmtime host
# takes with --dir, with descriptor 3 closed, and with descriptor 3 a file, which the Wasmtime host
# ignores, the executable's output and status must equal the Wasmtime host's.  With standard input
# closed and descriptor 3 a directory, the executable must end with status 67 and write nothing,
# and on the host's processor strace must show that the startup's openat returned descriptor 0 and
# that exit_group(67) followed it.  On the host's processor, strace must show the startup's openat
# of descriptor 3 with the path in the shim's scratch, 1,080 bytes above the scratch at the end of
# the area of 4,096 pages, and the flags 0x84000, and the close of the descriptor that it returns.
# strace's fault injection then makes openat return EPERM, EACCES, and descriptor 3, and close
# return 5, each of which must end the run with status 67, no output, and no call between the
# startup's calls and exit_group(67), so that the status comes from the startup routine and not
# from the guest.  Injected EIO from close must give the output of the run with the directory.
# The products lie in OUT, build/linux/a64-wasi-preopen unless set.  With --runs DIR, the script
# builds and checks nothing and runs the executables and modules that an earlier run left in DIR, on
# a host that needs neither Lean nor wasm-tools.
# Usage: tests/linux/a64-wasi-preopen.sh [--runs DIR]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
qemu=${QEMU_USER:-/usr/bin/qemu-aarch64}
host=${HOST:-$root/build/tools/leanexe-wasmtime-host}
status=0
if [ "${1:-}" = --runs ] && [ -n "${2:-}" ]; then
  out=$(realpath "$2")
elif [ $# -eq 0 ]; then
  out=$(realpath -m "${OUT:-$root/build/linux/a64-wasi-preopen}")
  rm -rf "${out:?}"
  mkdir -p "$out"
  tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build a64-wasi \
    TestSupport.A64.WasiElf Verified.Examples.WasiPrestatNative LeanExe.A64.File
  tools/leanrun --timeout 30m lake env .lake/build/bin/a64-wasi emit "$out" || status=1
  wasm-tools parse tests/linux/wasi/prestat-numbers.wat -o "$out/numbers.wasm"
  tools/leanrun --timeout 30m lake env .lake/build/bin/a64-wasi wasm "$out/numbers.wasm" \
    "$out/numbers.elf" || status=1
  tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiPrestat \
    Verified.Examples.WasiPrestat.command.module "$out/prestat.wasm"
  if tools/leanrun --timeout 60m --memory-high 12G lake env sh -c 'cd "$1" && lean "$2"' sh \
      "$out" "$root/tests/TestSupport/A64/ImageFilesWasiPrestat.lean" >"$out/check.log" 2>&1 &&
      [ "$(grep -c "depends on axioms\|does not depend on any axioms" "$out/check.log")" = 6 ] &&
      ! grep "depends on axioms" "$out/check.log" |
        sed 's/.*depends on axioms: \[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
        grep -qvx 'propext\|Classical.choice\|Quot.sound'; then
    echo "pass: the kernel's check of ImageFilesWasiPrestat.lean"
  else
    echo "fail: the kernel's check of ImageFilesWasiPrestat.lean: $(head -c 600 "$out/check.log")"
    status=1
  fi
else
  echo "usage: tests/linux/a64-wasi-preopen.sh [--runs DIR]" >&2
  exit 2
fi
if [ ! -x "$host" ]; then
  echo "fail: the Wasmtime host $host is missing"
  exit 1
fi
chmod +x "$out/prestat.elf" "$out/numbers.elf"
dir=$out/granted
mkdir -p "$dir"
printf 'x' >"$out/file"
# Runs the command given as arguments within the time limit.
limited() {
  timeout "${TIMEOUT:-60}" "$@"
}
# Compares the run named $1 with status $2 and output $3 against the status $4 and output $5.
same() {
  if [ "$2" -eq "$4" ] && cmp -s "$3" "$5"; then
    echo "pass: $1: status $2 and $(stat -c %s "$3") bytes, as the Wasmtime host gives"
  else
    echo "fail: $1: status $2 and $(stat -c %s "$3") bytes, where the Wasmtime host gives" \
      "status $4 and $(stat -c %s "$5") bytes"
    status=1
  fi
}
# Requires the run named $1 to end with status $2, 67, and to write nothing to the file $3.
refused() {
  if [ "$2" -eq 67 ] && [ ! -s "$3" ]; then
    echo "pass: $1: status 67, nothing written"
  else
    echo "fail: $1: status $2 and $(stat -c %s "$3") bytes, where 67 and nothing are due"
    status=1
  fi
}
# Requires the strace log $2 of the run named $1 to show the executable's execve, the startup's
# calls $3, and exit_group(67), and no other call.
startup_exit() {
  local calls
  calls=$(sed -n 's/^[0-9]* *\([a-z0-9_]*\)(.*/\1/p' "$2" | tr '\n' ' ')
  if [ "$calls" = "execve $3 exit_group " ] && grep -q '^[0-9]* *exit_group(67)' "$2"; then
    echo "pass: $1: strace shows execve, $3, and exit_group(67)"
  else
    echo "fail: $1: strace shows the calls $calls"
    status=1
  fi
}
# The address of the path buffer of the shim's scratch in the executable $1: the data segment's
# address, from its program header, plus the area of 4,096 pages and 1,080.
pathAddress() {
  local area
  area=$(od -An -tu8 -j 136 -N 8 "$1" | tr -d ' ')
  printf '0x%x' $((area + 4096 + 4096 * 65536 + 1080))
}
for name in prestat numbers; do
  elf=$out/$name.elf
  wasm=$out/$name.wasm
  for case in granted closed file; do
    code=0
    case $case in
      granted) limited "$host" --dir "$dir" --stdin-file /dev/null \
          --stdout-file "$out/wasmtime-$name-$case.out" run "$wasm" \
          2>"$out/wasmtime-$name-$case.err" || code=$?;;
      *) limited "$host" --stdin-file /dev/null --stdout-file "$out/wasmtime-$name-$case.out" \
          run "$wasm" 2>"$out/wasmtime-$name-$case.err" || code=$?;;
    esac
    want=$code
    for how in native qemu; do
      if [ "$how" = native ]; then set -- "$elf"; else set -- "$qemu" "$elf"; fi
      run=$out/$how-$name-$case.out
      code=0
      case $case in
        granted) limited "$@" </dev/null >"$run" 3<"$dir" || code=$?;;
        closed) limited "$@" </dev/null >"$run" 3<&- || code=$?;;
        file) limited "$@" </dev/null >"$run" 3<"$out/file" || code=$?;;
      esac
      same "$name $how, descriptor 3 $case" "$code" "$run" "$want" \
        "$out/wasmtime-$name-$case.out"
    done
  done
  for how in native qemu; do
    if [ "$how" = native ]; then set -- "$elf"; else set -- "$qemu" "$elf"; fi
    code=0
    limited "$@" <&- >"$out/$how-$name-stdin.out" 3<"$dir" || code=$?
    refused "$name $how, standard input closed" "$code" "$out/$how-$name-stdin.out"
  done
  # strace writes to standard error, so that its own descriptors leave descriptor 0 free.
  log=$out/strace-$name-stdin.log
  code=0
  limited strace -e raw=openat,close "$elf" <&- >"$out/strace-$name-stdin.out" 2>"$log" \
    3<"$dir" || code=$?
  first=$(grep -m1 '^openat(' "$log" || true)
  fd=$(printf '%s' "$first" | sed -n 's/.*= \(0x[0-9a-f]*\|[0-9]*\)$/\1/p')
  call=$(printf '%s' "$first" | sed 's/ *= .*$//')
  if [ "$code" -eq 67 ] &&
      [ "$call" = "openat(0x3, $(pathAddress "$elf"), 0x84000, 0)" ] &&
      [ -n "$fd" ] && [ "$((fd))" -eq 0 ]; then
    startup_exit "$name, standard input closed" "$log" "openat"
  else
    echo "fail: $name, standard input closed: status $code, startup's openat $first"
    status=1
  fi
  # The startup's calls as strace shows them, with each argument raw.
  log=$out/strace-$name.log
  code=0
  limited strace -f -e trace=openat,close -e raw=openat,close -o "$log" "$elf" </dev/null \
    >"$out/strace-$name.out" 3<"$dir" || code=$?
  first=$(grep -m1 ' openat(' "$log" | sed 's/^[0-9]* *//')
  fd=$(printf '%s' "$first" | sed -n 's/.*= \(0x[0-9a-f]*\)$/\1/p')
  call=$(printf '%s' "$first" | sed 's/ *= .*$//')
  if [ "$code" -eq 0 ] &&
      [ "$call" = "openat(0x3, $(pathAddress "$elf"), 0x84000, 0)" ] &&
      [ -n "$fd" ] && [ "$((fd))" -ge 4 ] &&
      grep -q "^[0-9]* *close($fd) *= 0$" "$log" &&
      cmp -s "$out/strace-$name.out" "$out/native-$name-granted.out"; then
    echo "pass: $name: the startup's openat of the scratch's path and close of descriptor $((fd))"
  else
    echo "fail: $name: the startup's calls: $(head -c 400 "$log")"
    status=1
  fi
  for fault in openat:error=EPERM openat:error=EACCES openat:retval=3 close:retval=5; do
    code=0
    limited strace -f -e inject="$fault" -o "$out/strace-$name-$fault.log" \
      "$elf" </dev/null >"$out/fault-$name-$fault.out" 3<"$dir" || code=$?
    refused "$name with $fault injected" "$code" "$out/fault-$name-$fault.out"
    case $fault in
      openat:*) calls=openat;;
      *) calls="openat close";;
    esac
    startup_exit "$name with $fault injected" "$out/strace-$name-$fault.log" "$calls"
  done
  code=0
  limited strace -f -e trace=openat,close -e inject=close:error=EIO \
    -o "$out/strace-$name-close-eio.log" "$elf" </dev/null >"$out/fault-$name-close-eio.out" \
    3<"$dir" || code=$?
  same "$name with close:error=EIO injected" "$code" "$out/fault-$name-close-eio.out" 0 \
    "$out/wasmtime-$name-granted.out"
done
exit "$status"
