#!/bin/sh
# Usage: elaborate.sh REPO_COPY LEAN_SAIL PROJECT LIB [TARGET]
# Elaborates the Lean output of Sail's back end with the toolchain and packages of REPO_COPY, a
# scratch copy of this repository whose .lake/packages are built.  Copies lean-sail's sources
# (LEAN_SAIL) and the generated Lake project's sources (PROJECT, root module LIB) to
# REPO_COPY/tmp/sail, edits the latter with fix-output.sh, appends a lean_lib for each to
# REPO_COPY's lakefile, and builds TARGET (default LIB).  The appended libraries change only the
# copy's lakefile.
set -eu
repo=$1
leansail=$2
project=$3
lib=$4
target=${5:-$lib}
dest=$repo/tmp/sail
mkdir -p "$dest/lean-sail" "$dest/$lib"
cp -R "$leansail/Sail.lean" "$leansail/Sail" "$dest/lean-sail/"
cp -R "$project/$lib.lean" "$project/$lib" "$dest/$lib/"
sh "$(dirname "$0")/fix-output.sh" "$dest/$lib" "$lib"
if ! grep -q '^lean_lib Sail where' "$repo/lakefile.lean"; then
  cat >>"$repo/lakefile.lean" <<'EOF'

lean_lib Sail where
  srcDir := "tmp/sail/lean-sail"
EOF
fi
if ! grep -q "^lean_lib $lib where" "$repo/lakefile.lean"; then
  cat >>"$repo/lakefile.lean" <<EOF

lean_lib $lib where
  srcDir := "tmp/sail/$lib"
  moreLeanArgs := #["--tstack=400000"]
EOF
fi
cd "$repo"
lake build "$target"
