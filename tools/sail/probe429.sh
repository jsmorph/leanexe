#!/bin/sh
# Usage: probe429.sh PROJECT DEST
# Copies the Lake project PROJECT that Sail's Lean back end wrote (Float-valued reals, so that it
# needs no Mathlib) to DEST, which must not exist, edits it with fix-output.sh, and builds it
# with the toolchain and lean-sail revision that the back end names (Lean v4.29.0, lean-sail v6).
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project=$1
dest=$2
lib=$(sed -n 's/^defaultTargets = \["\(.*\)"\]$/\1/p' "$project/lakefile.toml")
if [ -e "$dest" ]; then
  echo "probe429.sh: $dest exists" >&2
  exit 1
fi
cp -R "$project" "$dest"
sh "$here/fix-output.sh" "$dest" "$lib"
sh "$here/lake-build.sh" "$dest"
