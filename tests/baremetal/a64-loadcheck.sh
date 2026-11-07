#!/usr/bin/env bash
# The check that QEMU's virt machine loads an arm64 Linux Image
# (https://www.kernel.org/doc/html/latest/arch/arm64/booting.html) where hw/arm/boot.c of QEMU 8.2
# places it.  QEMU copies the whole file to 0x40000000, the base of RAM, plus an offset: the
# header's text_offset when its image_size is not 0, with 2 MiB added when text_offset is below
# 4 KiB, where QEMU's boot stub lies, and 0x80000 when image_size is 0.  The header must hold the
# magic "ARM\x64" at offset 56.  QEMU starts stopped with -S, with the machine, the CPU, and the
# 1 GiB of RAM of bm_run in tests/baremetal/qemu.sh, and its monitor on standard input saves the
# bytes of guest RAM over the file's length at that address with pmemsave and then quits.  Under -S
# the CPU has run no instruction, and RAM holds what QEMU's reset placed there.  The saved bytes
# must equal the file.  ACCEL selects the accelerator, as qemu.sh describes, and QEMU runs within
# TIMEOUT seconds, 60 unless set.  The script prints one line, pass or fail, and exits with status
# 0 or 1.
# Usage: tests/baremetal/a64-loadcheck.sh IMAGE
set -euo pipefail
[ "$#" -eq 1 ] || { echo "usage: tests/baremetal/a64-loadcheck.sh IMAGE" >&2; exit 2; }
image=$1
source "$(dirname "$0")/qemu.sh"
u64() { od -An -tu8 --endian=little -j "$1" -N 8 "$image" | tr -d ' '; }
if [ "$(od -An -tx1 -j 56 -N 4 "$image" | tr -d ' ')" != 41524d64 ]; then
  echo "fail: $image: the header does not hold the magic ARM\x64 at offset 56"
  exit 1
fi
size=$(stat -c %s "$image")
if [ "$(u64 16)" = 0 ]; then
  offset=$((0x80000))
else
  offset=$(u64 8)
  if [ "$offset" -lt 4096 ]; then
    offset=$((offset + 0x200000))
  fi
fi
addr=$(printf '0x%x' $((0x40000000 + offset)))
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
qcode=0
printf 'pmemsave %s %s "%s"\nquit\n' "$addr" "$size" "$tmp/guest-ram" |
  timeout "${TIMEOUT:-60}" "$qemu" -M virt "${bm_cpu[@]}" -m 1G -display none -S \
    -monitor stdio -serial none -kernel "$image" >/dev/null 2>"$tmp/stderr" || qcode=$?
if [ "$qcode" -ne 0 ]; then
  echo "fail: $image: QEMU exited with status $qcode: $(head -c 300 "$tmp/stderr" | tr '\n' ' ')"
  exit 1
fi
if ! diff=$(cmp "$image" "$tmp/guest-ram" 2>&1); then
  echo "fail: $image: guest RAM at $addr differs from the file: $diff"
  exit 1
fi
echo "pass: $image: $size bytes at $addr"
