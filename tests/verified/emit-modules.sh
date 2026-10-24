#!/usr/bin/env bash
# Writes every module of tests/verified/modules.txt into DIR, as DIR/NAME.wasm with NAME the
# third field of its line.  With --compare BASELINE, it then compares each written file with the
# file of the same name in BASELINE and fails unless every pair is identical, so that a change to
# the compiler can be checked to leave existing modules unchanged.  Build the modules' targets
# first, for example with the targets of the first field.
# Usage: tests/verified/emit-modules.sh DIR [--compare BASELINE]
set -euo pipefail
if [ "$#" -ne 1 ] && { [ "$#" -ne 3 ] || [ "$2" != "--compare" ]; }; then
  echo "usage: tests/verified/emit-modules.sh DIR [--compare BASELINE]" >&2
  exit 2
fi
out=$1
baseline=${3:-}
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
mkdir -p "$out"
while IFS=: read -r module constant name; do
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$module" "$constant" \
    "$out/$name.wasm"
done <"$root/tests/verified/modules.txt"
if [ -z "$baseline" ]; then
  exit 0
fi
same=0
differ=0
while IFS=: read -r _ _ name; do
  if [ ! -f "$baseline/$name.wasm" ]; then
    echo "missing: $baseline/$name.wasm"
    differ=$((differ + 1))
  elif cmp -s "$baseline/$name.wasm" "$out/$name.wasm"; then
    same=$((same + 1))
  else
    echo "differs: $name.wasm"
    differ=$((differ + 1))
  fi
done <"$root/tests/verified/modules.txt"
echo "modules: $same identical, $differ different or missing"
[ "$differ" -eq 0 ]
