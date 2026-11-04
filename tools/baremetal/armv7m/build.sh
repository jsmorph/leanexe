#!/usr/bin/env bash
# Builds a program for QEMU's mps2-an500, a Cortex-M7, without libc, from C files and objects, with
# the startup code, its reports, and the linker script of this directory.  CompCert compiles every C
# file, the startup code included, and links the objects with -nostdlib, to which it appends its
# run-time library, libcompcert.a (driver/Linker.ml, lines 21 to 30), whose functions the code for
# 64-bit integers calls.  It compiles the inputs with -fno-common, so that a global without an
# initializer, such as lx_mem, is a definition in .bss.  The object of each C file lies beside OUT,
# named OUT, a dot, the file's base name, and .o.  CCOMP names CompCert 3.18's driver configured
# armv7m-eabihf, and CCOMP_STDLIB, when set, names the directory of its run-time library for a tree
# that is not installed.  OBJDUMP and NM name objdump and nm for ARM, arm-none-eabi-objdump and
# arm-none-eabi-nm by default.  STACK_SIZE is the size of the stack in bytes, 0x100000 by default.
# The arguments after -- are passed to the preprocessor of the startup code, for example -DNO_FPEN.
# After the link the script writes OUT.helpers, the lines of nm for the image's symbols that
# libcompcert.a defines, the run-time functions that the image contains, and prints them.  When
# STACK_DEPTHS names the list of the functions that take the call depth, as native-verified and
# native-bare write it, every input must be a C file: the script also compiles each to assembly
# beside OUT, named as its object with .s for .o, writes the image's disassembly as OUT.dis, and
# fails, removing the image, unless stack-bound.sh of this directory bounds the stack of main within
# STACK_SIZE, writing the bound as OUT.bound, and unless access-check.sh of this directory shows
# each instruction of the image that requires a word-aligned address safe, writing its summary as
# OUT.access.
# Usage: tools/baremetal/armv7m/build.sh OUT INPUT... [-- -DNAME...]
set -euo pipefail
usage() {
  echo "usage: tools/baremetal/armv7m/build.sh OUT INPUT... [-- -DNAME...]" >&2
  exit 2
}
[ "$#" -ge 2 ] || usage
out=$1
shift
inputs=()
while [ "$#" -gt 0 ] && [ "$1" != "--" ]; do
  inputs+=("$1")
  shift
done
[ "${#inputs[@]}" -gt 0 ] || usage
if [ "$#" -gt 0 ]; then
  shift
fi
here=$(cd "$(dirname "$0")" && pwd)
ccomp=${CCOMP:-ccomp}
nm=${NM:-arm-none-eabi-nm}
objdump=${OBJDUMP:-arm-none-eabi-objdump}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
  lib=$CCOMP_STDLIB/libcompcert.a
else
  lib=$(dirname "$(command -v "$ccomp")")/../lib/compcert/libcompcert.a
fi
stack=${STACK_SIZE:-0x100000}
"$ccomp" "${stdlib[@]}" "$@" -c "$here/start.S" -o "$out.start.o"
"$ccomp" "${stdlib[@]}" -c "$here/report.c" -o "$out.report.o"
objects=("$out.start.o" "$out.report.o")
for input in "${inputs[@]}"; do
  case "$input" in
    *.c)
      object=$out.$(basename "${input%.c}").o
      "$ccomp" "${stdlib[@]}" -fno-common -c "$input" -o "$object"
      objects+=("$object")
      ;;
    *.o)
      objects+=("$input")
      ;;
    *)
      echo "tools/baremetal/armv7m/build.sh: $input is neither a C file nor an object" >&2
      exit 2
      ;;
  esac
done
"$ccomp" "${stdlib[@]}" -nostdlib -static -T "$here/link.ld" -Wl,--build-id=none \
  -Wl,--defsym,STACK_SIZE="$stack" "${objects[@]}" -o "$out"
names=$("$nm" --defined-only "$lib" | awk 'NF == 3 && $2 ~ /^[A-Z]$/ { print $3 }' | paste -sd' ')
"$nm" "$out" | awk -v names="$names" '
  BEGIN { n = split(names, a, " "); for (i = 1; i <= n; i++) helper[a[i]] = 1 }
  NF == 3 && ($3 in helper)
' | sort >"$out.helpers"
cat "$out.helpers"
if [ -n "${STACK_DEPTHS:-}" ]; then
  asm=()
  for input in "${inputs[@]}"; do
    case "$input" in
      *.c)
        s=$out.$(basename "${input%.c}").s
        "$ccomp" "${stdlib[@]}" -fno-common -S "$input" -o "$s"
        asm+=("$s")
        ;;
      *)
        echo "tools/baremetal/armv7m/build.sh: with STACK_DEPTHS, $input is not a C file" >&2
        rm -f "$out"
        exit 2
        ;;
    esac
  done
  "$objdump" -d --no-show-raw-insn "$out" >"$out.dis"
  if ! "$here/stack-bound.sh" -r main -l "$((stack))" -d "$out.dis" "$STACK_DEPTHS" "${asm[@]}" \
      >"$out.bound" || ! "$here/access-check.sh" "$out.dis" >"$out.access"; then
    rm -f "$out"
    exit 1
  fi
fi
