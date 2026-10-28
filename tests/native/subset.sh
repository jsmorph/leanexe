#!/usr/bin/env bash
# Checks that every module of the verified corpus, tests/verified/modules.txt, is in the subset of
# WebAssembly that the translator to C accepts (LeanExe/Native/Subset.lean).  Each check loads the
# built module, so run `tools/leanrun --memory-high 10G --timeout 12h lake build Verified Library`
# first.  LEANRUN_MEMORY_HIGH is the memory limit of each step that runs under tools/leanrun, 8G
# unless the caller sets it.  The largest step measured, the check of the largest corpus module,
# keeps 5.5 GB resident.
# Usage: tests/native/subset.sh
set -euo pipefail
export LEANRUN_MEMORY_HIGH=${LEANRUN_MEMORY_HIGH:-8G}
if [ "$#" -ne 0 ]; then
  echo "usage: tests/native/subset.sh" >&2
  exit 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
tools/leanrun --timeout 30m lake build LeanExe.Native.Subset
inside=0
outside=0
while IFS=: read -r module constant name; do
  if tools/leanrun --timeout 10m lake env lean --run tools/Subset.lean "$module" "$constant" \
      </dev/null; then
    inside=$((inside + 1))
  else
    echo "fail: $name" >&2
    outside=$((outside + 1))
  fi
done <"$root/tests/verified/modules.txt"
echo "subset: $inside modules inside, $outside outside"
[ "$outside" -eq 0 ]
