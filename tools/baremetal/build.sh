#!/usr/bin/env bash
# Builds a C program for QEMU's virt machine for AArch64, without libc, with the startup code,
# its reports, and the linker script of this directory (docs/native-bare-metal.md).  CompCert
# compiles every file, the startup code included, and links them with -nostdlib.  The objects
# lie beside OUT, named OUT.program.o, OUT.report.o, and OUT.start.o.  CCOMP names CompCert
# 3.18's driver configured for aarch64-linux, and CCOMP_STDLIB, when set, names the directory of
# its run-time library for a tree that is not installed.  STACK_SIZE is the size of the stack in
# bytes, 0x100000 by default.  The arguments after OUT go to the preprocessor of the startup code,
# for example -DNO_FPEN.
# Usage: tools/baremetal/build.sh PROGRAM.c OUT [-DNAME...]
set -euo pipefail
if [ "$#" -lt 2 ]; then
  echo "usage: tools/baremetal/build.sh PROGRAM.c OUT [-DNAME...]" >&2
  exit 2
fi
program=$1
out=$2
shift 2
here=$(cd "$(dirname "$0")" && pwd)
ccomp=${CCOMP:-ccomp}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
stack=${STACK_SIZE:-0x100000}
"$ccomp" "${stdlib[@]}" -c "$program" -o "$out.program.o"
"$ccomp" "${stdlib[@]}" -c "$here/report.c" -o "$out.report.o"
"$ccomp" "${stdlib[@]}" "$@" -c "$here/start.S" -o "$out.start.o"
"$ccomp" "${stdlib[@]}" -nostdlib -static -T "$here/link.ld" -Wl,--defsym,STACK_SIZE="$stack" \
  "$out.start.o" "$out.report.o" "$out.program.o" -o "$out"
