#!/usr/bin/env bash
# Builds a program for QEMU's virt machine for AArch64, without libc, from C files and objects,
# with the startup code, its reports, and the linker script of this directory
# (docs/native-bare-metal.md).  CompCert compiles every C file, the startup code included, and
# links the objects with -nostdlib.  The object of each C file lies beside OUT, named OUT, a dot,
# the file's base name, and .o.  CCOMP names CompCert 3.18's driver configured for aarch64-linux,
# and CCOMP_STDLIB, when set, names the directory of its run-time library for a tree that is not
# installed.  STACK_SIZE is the size of the stack in bytes, 0x100000 by default.  The arguments
# after -- go to the preprocessor of the startup code, for example -DNO_FPEN.
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
      "$ccomp" "${stdlib[@]}" -c "$input" -o "$object"
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
"$ccomp" "${stdlib[@]}" -nostdlib -static -T "$here/link.ld" -Wl,--build-id=none \
  -Wl,--defsym,STACK_SIZE="$stack" "${objects[@]}" -o "$out"
