#!/usr/bin/env bash
# The translator's end-to-end test.  It builds the native theorems of
# tests/TestSupport/Native/*Native.lean, which the kernel checks.  The executable native-emit
# (tests/TestSupport/Native/Emit.lean) translates each module of its cases to C and writes a host
# program for each, with the lines that Talos's run gives for the host's calls.  clightgen reads
# each C file back, and native-emit check compares the Clight it wrote with the translation.
# ccomp then compiles each translation with its host, and the program must print the expected
# lines.  CCOMP and CLIGHTGEN name CompCert 3.18's driver and clightgen, built from one tree for
# the machine that runs the test, and CCOMP_STDLIB, when set, names the directory of CompCert's
# run-time library for a tree that is not installed.
# LEANRUN_MEMORY_HIGH is the memory limit of each step that runs under tools/leanrun, 6G unless
# the caller sets it.  The largest step measured, the elaboration of a native theorem file that
# the build compiles, keeps 3.7 GB resident.
# Usage: tests/native/run.sh
set -euo pipefail
export LEANRUN_MEMORY_HIGH=${LEANRUN_MEMORY_HIGH:-6G}
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$root/build/native/run
cd "$root"
tools/leanrun --timeout 90m lake build native-emit TestSupport.Native.GcdNative \
  TestSupport.Native.ExamplesNative TestSupport.Native.EulerNative TestSupport.Native.Gpt32Native
rm -rf "$out"
tools/leanrun --timeout 30m .lake/build/bin/native-emit emit "$out"
names=$(tools/leanrun --timeout 5m .lake/build/bin/native-emit names)
for name in $names; do
  (cd "$out" && "$clightgen" "$name.c")
done
tools/leanrun --timeout 10m .lake/build/bin/native-emit check "$out"
status=0
for name in $names; do
  "$ccomp" "${stdlib[@]}" -o "$out/$name" "$out/$name.c" "$out/${name}_host.c"
  if "$out/$name" > "$out/$name.out" && diff "$out/$name.expected" "$out/$name.out"; then
    echo "native: $name: $(wc -l < "$out/$name.out") calls agree with Talos"
  else
    echo "native: $name: the native program differs from Talos" >&2
    status=1
  fi
done
exit $status
