#!/usr/bin/env bash
# The check of `native-verified build --aligned` (tests/TestSupport/Native/Verified.lean) against
# the theorems of a module.  It must compile tests/TestSupport/Native/AlignedCrc.lean, the CRC
# programs compiled with verified_compile.alignedNative, and it must refuse
# Library.Hashing.Crc.Compiled, the same programs compiled without the option, and
# Verified.Examples.Literals, a program with byte literals.  A refusal must exit with status 4,
# name the missing theorem or the literals, and write no file.  The script prints one line per
# module and fails unless each gives the expected result.  CCOMP and CLIGHTGEN are as for
# tests/native/run.sh.  LEANRUN_MEMORY_HIGH is the memory limit of each step that runs under
# tools/leanrun, 6G unless the caller sets it.
# Usage: tests/native/aligned.sh
set -euo pipefail
export LEANRUN_MEMORY_HIGH=${LEANRUN_MEMORY_HIGH:-6G}
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$root/build/native/aligned
cd "$root"
tools/leanrun --timeout 60m lake build native-verified TestSupport.Native.AlignedCrc \
  Library.Hashing.Crc.Compiled Verified.Examples.Literals
rm -rf "$out"
mkdir -p "$out"
status=0
# build MODULE CONSTANT NAME: the aligned build of one module, its status in `code`.
build() {
  code=0
  CLIGHTGEN=$clightgen CCOMP=$ccomp tools/leanrun --timeout 10m lake env \
    .lake/build/bin/native-verified build --aligned "$1" "$2" "$3" "$out" \
    >"$out/$3.log" 2>&1 || code=$?
}
build TestSupport.Native.AlignedCrc TestSupport.Native.AlignedCrc.compiled.module crcaligned
if [ "$code" -eq 0 ] && [ -f "$out/crcaligned.o" ]; then
  echo "aligned: crcaligned built: $(grep -c . "$out/crcaligned.exports") exports"
else
  echo "fail: crcaligned: status $code: $(cat "$out/crcaligned.log")"
  status=1
fi
# refused MODULE CONSTANT NAME TEXT: the aligned build must refuse with status 4 and TEXT.
refused() {
  build "$1" "$2" "$3"
  if [ "$code" -eq 4 ] && grep -qF "$4" "$out/$3.log" && [ ! -e "$out/$3.c" ]; then
    echo "aligned: $3 refused: $(grep -c 'refusing' "$out/$3.log") reasons"
  else
    echo "fail: $3: status $code, expected 4 and \"$4\": $(cat "$out/$3.log")"
    status=1
  fi
}
refused Library.Hashing.Crc.Compiled Library.Hashing.Crc.compiled.module crc \
  "Library.Hashing.Crc.compiled.translationAligned_eq is missing"
refused Verified.Examples.Literals Verified.Examples.Literals.compiled.module literals \
  "the program has byte literals"
exit "$status"
