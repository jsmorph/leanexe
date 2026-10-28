#!/usr/bin/env bash
# Builds a program for QEMU's virt machine for AArch64, without libc, from C files and objects,
# with the startup code, its reports, and the linker script of this directory
# (docs/native-bare-metal.md).  CompCert compiles every C file, the startup code included, and
# links the objects with -nostdlib.  It compiles the inputs with -fno-common, so that a global
# without an initializer, such as lx_mem, is a definition in .bss that the code addresses
# directly rather than through the global offset table.  The object of each C file lies beside
# OUT, named OUT, a dot, the file's base name, and .o.  CCOMP names CompCert 3.18's driver
# configured for aarch64-linux, and CCOMP_STDLIB, when set, names the directory of its run-time
# library for a tree that is not installed.  STACK_SIZE is the size of the stack in bytes,
# 0x100000 by default.  The arguments
# after -- go to the preprocessor of the startup code, for example -DNO_FPEN.  When STACK_DEPTHS
# names the list of the functions that take the call depth, as native-verified and native-bare
# write it, every input must be a C file: the script also compiles each to assembly beside OUT,
# named as its object with .s for .o, and fails unless tools/baremetal/stack-bound.sh bounds the
# stack of main within STACK_SIZE, writing the bound as OUT.bound, and unless
# tools/baremetal/access-check.sh finds no instruction that requires an aligned access.
# Usage: tools/baremetal/build.sh OUT INPUT... [-- -DNAME...]
set -euo pipefail
usage() {
  echo "usage: tools/baremetal/build.sh OUT INPUT... [-- -DNAME...]" >&2
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
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
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
      echo "tools/baremetal/build.sh: $input is neither a C file nor an object" >&2
      exit 2
      ;;
  esac
done
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
        echo "tools/baremetal/build.sh: with STACK_DEPTHS, $input is not a C file" >&2
        exit 2
        ;;
    esac
  done
  "$here/stack-bound.sh" -r main -l "$((stack))" "$STACK_DEPTHS" "${asm[@]}" >"$out.bound"
  "$here/access-check.sh" "${asm[@]}"
fi
"$ccomp" "${stdlib[@]}" -nostdlib -static -T "$here/link.ld" -Wl,--build-id=none \
  -Wl,--defsym,STACK_SIZE="$stack" "${objects[@]}" -o "$out"
