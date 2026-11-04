#!/usr/bin/env bash
# The startup code of tools/baremetal/armv7m and the controller programs on QEMU's mps2-an500, a
# Cortex-M7, without Lean.  DIR holds the files that native-bare emit-ctl writes for each
# program NAME: NAME.c, NAME.depth, NAME.in, and NAME.expected (tests/baremetal/ctl.sh).
#
# QEMU's memory map, from its monitor's "info mtree", must place ZBT SSRAM1 and SSRAM2 and 3 at
# the CODE and SRAM regions of tools/baremetal/armv7m/link.ld, PSRAM's 16 MiB at lx_in, and
# UART0 at lx_out.  tests/baremetal/m7probe.c must print the words of m7probe.expected and exit
# with status 42 through semihosting, with a high-water mark of 16,032 bytes, which must equal
# the static bound of its main, and its object may name no undefined symbol but lx_out and
# CompCert's run-time functions.  With an unaligned word load before main it must do the same.
# Without the floating-point enable it must stop at UsageFault, exception 6, with NOCP in CFSR,
# and with an unaligned LDRD before main at UsageFault with UNALIGNED, which access-check.sh
# must report.  With a store to the word below the stack it must stop at MemManage, exception
# 4, with DACCVIOL and MMARVALID in CFSR and that word's address in MMFAR.  With a stack of 8
# KiB, below its bound, it must stop at MemManage with DACCVIOL, MMARVALID, and MSTKERR, the
# failed stacking of the exception's frame on the full stack, and an address of the guard in
# MMFAR.  Each of these faults ends with status 255.  With the UART's transmitter and receiver
# disabled, it must write nothing and exit with status 42.
#
# Each program NAME of DIR is built with tools/baremetal/armv7m/build.sh, whose stack bound and
# access check must hold, and runs in its own QEMU process, with QEMU's generic loader placing
# NAME.in at lx_in.  main never returns, so once the UART output reaches the size of
# NAME.expected, eight bytes per window, QEMU stops and must exit with status 0, and the output
# must equal NAME.expected.  The products lie in OUT, build/baremetal/m7 unless set.  CCOMP and
# CCOMP_STDLIB are as for build.sh, QEMU names qemu-system-arm, OBJDUMP and NM name objdump and
# nm for ARM, and TIMEOUT, 120 unless set, bounds each run in seconds.
# Usage: tests/baremetal/m7.sh DIR
set -euo pipefail
if [ "$#" -ne 1 ]; then
  echo "usage: tests/baremetal/m7.sh DIR" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
here=$root/tests/baremetal
tools=$root/tools/baremetal/armv7m
dir=$(cd "$1" && pwd)
out=${OUT:-$root/build/baremetal/m7}
qemu=${QEMU:-qemu-system-arm}
ccomp=${CCOMP:-ccomp}
nm=${NM:-arm-none-eabi-nm}
objdump=${OBJDUMP:-arm-none-eabi-objdump}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
rm -rf "$out"
mkdir -p "$out"
status=0

fail() {
  echo "fail: $1"
  status=1
}

ld=$tools/link.ld
uart=$(sed -n 's/^ *lx_out = \(0x[0-9a-fA-F]*\);$/\1/p' "$ld")
input=$(sed -n 's/^ *lx_in = \(0x[0-9a-fA-F]*\);$/\1/p' "$ld")

# Runs the image $1 with its UART output in the file $2 and the QEMU options after $2, within
# TIMEOUT seconds, and sets code to QEMU's exit status, the program's.
m7_run() {
  local image=$1 serial=$2
  shift 2
  rm -f "$serial"
  code=0
  timeout "${TIMEOUT:-120}" "$qemu" -M mps2-an500 -display none -monitor none \
    -serial "file:$serial" -semihosting-config enable=on,target=native "$@" -kernel "$image" \
    </dev/null || code=$?
}

# Runs the image $1 with the QEMU options after $3, as bm_stream of tests/baremetal/qemu.sh
# does, for a program that never ends: it copies the first $3 bytes of the UART output to the
# file $2 and then stops QEMU with SIGTERM, unless QEMU has exited.  code is QEMU's exit status,
# 0 after the stop and 124 after the timeout.
m7_stream() {
  local image=$1 serial=$2 bytes=$3 fifo=$2.fifo pid
  shift 3
  rm -f "$serial" "$fifo"
  mkfifo "$fifo"
  timeout "${TIMEOUT:-120}" "$qemu" -M mps2-an500 -display none -monitor none -serial stdio \
    -semihosting-config enable=on,target=native "$@" -kernel "$image" </dev/null >"$fifo" &
  pid=$!
  head -c "$bytes" "$fifo" >"$serial"
  rm "$fifo"
  kill "$pid" 2>/dev/null || :
  code=0
  wait "$pid" || code=$?
}

# Builds the image $out/$1 from m7probe.c with the startup code's defines after $1.
build() {
  local image=$1
  shift
  "$tools/build.sh" "$out/$image" "$here/m7probe.c" -- "$@" >"$out/$image.build" 2>&1
}

# The address $1 as QEMU's monitor prints it, sixteen hexadecimal digits.
addr() {
  printf '%016x' $(($1))
}

printf 'info mtree\nquit\n' | timeout "${TIMEOUT:-120}" "$qemu" -M mps2-an500 -display none \
  -monitor stdio -serial null -S 2>&1 | tr -d '\r' >"$out/mtree.txt"
# Succeeds when the memory tree has the region $1 from $2 for $3 bytes.
region() {
  grep -q "^ *$(addr "$2")-$(addr "$2 + $3 - 1") (prio 0, [a-z/]*): $1\$" "$out/mtree.txt"
}
for r in CODE:mps.ssram1 SRAM:mps.ssram23; do
  origin=$(sed -n "s/^ *${r%%:*} ([a-z]*) : ORIGIN = \(0x[0-9a-fA-F]*\), LENGTH = .*$/\1/p" "$ld")
  length=$(sed -n "s/^ *${r%%:*} ([a-z]*) : ORIGIN = .*, LENGTH = \(0x[0-9a-fA-F]*\)$/\1/p" "$ld")
  if ! region "${r#*:}" "$origin" "$length"; then
    fail "QEMU's memory tree has no ${r#*:} at $origin for $length bytes, the region ${r%%:*}"
  fi
done
if ! region mps.ram "$input" 0x1000000; then
  fail "QEMU's memory tree has no PSRAM of 16 MiB at lx_in, $input"
fi
if ! region uart "$uart" 0x1000; then
  fail "QEMU's memory tree has no UART at lx_out, $uart"
fi

if build probe.elf; then
  undefined=$("$nm" -u "$out/probe.elf.m7probe.o" |
    awk '$2 != "lx_out" && $2 !~ /^__compcert_i64_/' | paste -sd' ')
  if [ -n "$undefined" ]; then
    fail "m7probe.c names undefined symbols other than lx_out and run-time functions: $undefined"
  fi
  m7_run "$out/probe.elf" "$out/probe.serial"
  if [ "$code" != 42 ] || ! diff "$here/m7probe.expected" <(grep -v '^R:' "$out/probe.serial") ||
      ! grep -qx 'R:exit 42 stack 16032' "$out/probe.serial"; then
    fail "m7probe.c gave status $code and $(paste -sd' ' "$out/probe.serial")"
  fi
  echo lxf_depth >"$out/probe.depth"
  "$ccomp" "${stdlib[@]}" -fno-common -S "$here/m7probe.c" -o "$out/probe.s"
  "$objdump" -d --no-show-raw-insn "$out/probe.elf" >"$out/probe.dis"
  bound=$("$tools/stack-bound.sh" -r main -d "$out/probe.dis" "$out/probe.depth" "$out/probe.s")
  if [ "$bound" != "16032 main" ]; then
    fail "the static bound of m7probe.c's main is $bound, not its high-water mark of 16032 bytes"
  fi
else
  fail "m7probe.c did not build: $(head -n 3 "$out/probe.elf.build" | paste -sd' ')"
fi

# Builds the probe with the defines $2..., runs it, and fails with the description $1 unless the
# status is $s and, when $r is not empty, a line of the output matches the extended regular
# expression $r.  The image is named after the description.
check() {
  local what=$1 image
  shift
  image=$(echo "$what" | tr 'A-Z' 'a-z' | tr -c 'a-z0-9\n' '-').elf
  if ! build "$image" "$@"; then
    fail "the probe $what did not build: $(head -n 3 "$out/$image.build" | paste -sd' ')"
    return
  fi
  m7_run "$out/$image" "$out/$image.serial"
  if [ "$code" != "$s" ] || { [ -n "$r" ] && ! grep -Eq "$r" "$out/$image.serial"; }; then
    fail "the probe $what gave status $code and $(paste -sd' ' "$out/$image.serial")"
  fi
}

s=42 r='^R:exit 42 stack 16032$' check "after an unaligned load" -DUNALIGNED_TEST
if ! diff -q "$here/m7probe.expected" <(grep -v '^R:' "$out/after-an-unaligned-load.elf.serial") \
    >/dev/null; then
  fail "the probe after an unaligned load wrote other words"
fi
s=255 r='^R:fault 6 cfsr 0x00080000 ' check "without floating point" -DNO_FPEN
s=255 r='^R:fault 6 cfsr 0x01000000 ' check "after an unaligned ldrd" -DUNALIGNED_LDRD_TEST
if "$objdump" -d --no-show-raw-insn "$out/after-an-unaligned-ldrd.elf" >"$out/ldrd.dis" &&
    "$tools/access-check.sh" "$out/ldrd.dis" >"$out/ldrd.access" 2>&1; then
  fail "access-check.sh accepted the image with an unaligned ldrd"
elif ! grep -q '^access-check: _start: .*ldrd' "$out/ldrd.access"; then
  fail "access-check.sh did not report the ldrd of _start: $(paste -sd' ' "$out/ldrd.access")"
fi
# The value of the symbol $2 of the image $1, and the MMFAR that the image's report gives.
sym() {
  "$nm" "$out/$1" | awk -v s="$2" '$3 == s { print "0x" $1 }'
}
mmfar() {
  sed -n 's/^R:fault 4 cfsr 0x[0-9a-f]* hfsr 0x[0-9a-f]* mmfar \(0x[0-9a-f]*\) .*$/\1/p' \
    "$out/$1.serial"
}

s=255 r='^R:fault 4 cfsr 0x00000082 hfsr 0x00000000 ' check "after a store below the stack" \
  -DGUARD_TEST
image=after-a-store-below-the-stack.elf
if [ -f "$out/$image" ]; then
  want=$(printf '0x%08x' $(($(sym "$image" __stack_bottom) - 4)))
  if [ "$(mmfar "$image")" != "$want" ]; then
    fail "the probe after a store below the stack gave MMFAR $(mmfar "$image"), not $want"
  fi
fi
s=255 r='^R:fault 4 cfsr 0x00000092 hfsr 0x00000000 ' STACK_SIZE=0x2000 \
  check "with a stack of 8 KiB"
image=with-a-stack-of-8-kib.elf
if [ -f "$out/$image" ]; then
  a=$(mmfar "$image")
  guard=$(sym "$image" __stack_guard)
  if [ -z "$a" ] || [ $((a)) -lt $((guard)) ] || [ $((a)) -ge $((guard + 0x1000)) ]; then
    fail "the probe with a stack of 8 KiB faulted at ${a:-no address}, outside the guard at $guard"
  fi
fi
s=42 r='' check "without the UART" -DNO_UART
if [ -s "$out/without-the-uart.elf.serial" ]; then
  fail "the probe without the UART wrote $(paste -sd' ' "$out/without-the-uart.elf.serial")"
fi
if [ "$status" -eq 0 ]; then
  echo "pass: memory map, probe, unaligned, nofp, ldrd, guard, overflow, and no UART"
fi

for c in "$dir"/*.c; do
  name=$(basename "${c%.c}")
  [ -f "$dir/$name.expected" ] || continue
  if ! STACK_DEPTHS=$dir/$name.depth "$tools/build.sh" "$out/$name.elf" "$c" \
      >"$out/$name.build" 2>&1; then
    fail "$name: $(paste -sd' ' "$out/$name.build" | head -c 400)"
    continue
  fi
  n=$(stat -c %s "$dir/$name.expected")
  m7_stream "$out/$name.elf" "$out/$name.serial" "$n" \
    -device "loader,file=$dir/$name.in,addr=$input,force-raw=on"
  if [ "$code" != 0 ] || ! cmp -s "$dir/$name.expected" "$out/$name.serial"; then
    fail "$name: status $code, output $(od -An -tx1 "$out/$name.serial" | head -c 200)"
  else
    echo "pass: $name: $((n / 8)) windows, $n bytes, bound" \
      "$(cut -d' ' -f1 "$out/$name.elf.bound"), helpers" \
      "$(awk '{print $3}' "$out/$name.elf.helpers" | paste -sd' ')"
  fi
done
exit "$status"
