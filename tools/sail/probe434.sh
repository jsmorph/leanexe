#!/bin/sh
# Usage: probe434.sh REPO_COPY LEAN_SAIL OUT
# With the toolchain of REPO_COPY (see elaborate.sh), elaborates the real-number translation
# OUT/real/armv9fp and the translation OUT/rat/armv9rat with RatReal.lean in place of Sail's
# Float-valued reals, one after the other, and runs Eval.lean against Talos's functions.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=$1
leansail=$2
out=$3
sed 's/THE_MODULE_NAME/Armv9rat/g' "$here/RatReal.lean" >"$out/rat/armv9rat/Armv9rat/FakeReal.lean"
sh "$here/elaborate.sh" "$repo" "$leansail" "$out/real/armv9fp" Armv9fp
sh "$here/elaborate.sh" "$repo" "$leansail" "$out/rat/armv9rat" Armv9rat
cp "$here/Eval.lean" "$repo/tmp/sail/Eval.lean"
cd "$repo"
lake env lean tmp/sail/Eval.lean
