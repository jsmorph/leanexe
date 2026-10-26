#!/usr/bin/env bash
# The translator's end-to-end test on GCD (milestone M2).  The executable native-gcd
# (tests/TestSupport/Native/GcdEmit.lean) translates the two GCD modules of
# tests/TestSupport/Native/Gcd.lean to C and writes a host program for each, with the lines that
# Talos's run gives for the host's calls.  clightgen reads each C file back, and native-gcd check
# compares the Clight it wrote with the translation.  ccomp then compiles each translation with
# its host, and the program must print the expected lines.  CCOMP and CLIGHTGEN name CompCert
# 3.18's driver and clightgen, built from one tree for the machine that runs the test, and
# CCOMP_STDLIB, when set, names the directory of CompCert's run-time library for a tree that is
# not installed.
# Usage: tests/native/gcd.sh
set -euo pipefail
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$root/build/native/gcd
cd "$root"
tools/leanrun --timeout 60m lake build native-gcd
rm -rf "$out"
tools/leanrun --timeout 10m .lake/build/bin/native-gcd emit "$out"
for name in gcd_loop gcd_rec; do
  (cd "$out" && "$clightgen" "$name.c")
done
tools/leanrun --timeout 10m .lake/build/bin/native-gcd check "$out"
status=0
for name in gcd_loop gcd_rec; do
  "$ccomp" "${stdlib[@]}" -o "$out/$name" "$out/$name.c" "$out/${name}_host.c"
  if "$out/$name" > "$out/$name.out" && diff "$out/$name.expected" "$out/$name.out"; then
    echo "gcd: $name: $(wc -l < "$out/$name.out") calls agree with Talos"
  else
    echo "gcd: $name: the native program differs from Talos" >&2
    status=1
  fi
done
exit $status
