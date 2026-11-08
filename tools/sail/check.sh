#!/bin/sh
# Usage: check.sh [--record] SAIL_ARM LEAN_SAIL REPO_COPY WORK
# Regenerates Sail's Lean translation of the floating-point slice from pinned inputs and checks
# the proofs of F7/ against it.  SAIL_ARM is sail-arm at commit 7d0581642, LEAN_SAIL lean-sail at
# tag v6, REPO_COPY a scratch copy of this repository whose .lake/packages are built, and WORK a
# directory that the script creates.  Sail 0.20.3 must be in the opam switch sail-0.20.3.
#
# The script copies the model files that translate.sh reads and lean-sail's sources into WORK,
# applies lean-sail-v6.diff, translates the slice with the options of the real-number
# translation, and compares the SHA-256 hashes of the inputs, of the generated files, and of the
# files that fix-output.sh edits with check.sha256; with --record it writes check.sha256 instead.
# It then elaborates the translation and F7/ in REPO_COPY (elaborate.sh appends the libraries to
# REPO_COPY's lakefile), first with undefined_real returning an opaque constant, which the kernel
# cannot unfold, and then as generated, and after each prints the axioms of the theorems that
# Axioms.lean names and fails unless each depends on propext, Classical.choice, and Quot.sound
# at most.
set -eu
record=0
if [ "${1:-}" = "--record" ]; then
  record=1
  shift
fi
if [ "$#" -ne 4 ]; then
  echo "usage: check.sh [--record] SAIL_ARM LEAN_SAIL REPO_COPY WORK" >&2
  exit 2
fi
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
sailarm=$1
leansail=$2
repo=$3
work=$4
if [ -e "$work" ]; then
  echo "check.sh: $work exists" >&2
  exit 1
fi
version=$(opam exec --switch sail-0.20.3 -- sail --version)
case "$version" in
  "Sail 0.20.3 "*) ;;
  *) echo "check.sh: sail --version prints $version" >&2; exit 1 ;;
esac
echo "check.sh: $version"

# hashes DIR PATTERN LABEL: the hash of each file below DIR whose name matches PATTERN.
hashes() {
  (cd "$1" && find . -type f -name "$2" | LC_ALL=C sort | while read -r f; do
    printf '%s  %s/%s\n' "$(sha256sum "$f" | cut -d' ' -f1)" "$3" "${f#./}"
  done)
}

model=$work/arm-v9.4-a
mkdir -p "$model/src" "$work/lean-sail"
for f in prelude decode_start builtins v8_base stubs interrupts interface devices impdefs mem \
    decode_end fetch termination_measures; do
  cp "$sailarm/arm-v9.4-a/src/$f.sail" "$model/src/"
done
cp -R "$leansail/Sail.lean" "$leansail/Sail" "$work/lean-sail/"
patch -s -d "$work/lean-sail" -p1 <"$here/lean-sail-v6.diff"

opam exec --switch sail-0.20.3 -- sh "$here/translate.sh" "$model" "$work/out" armv9fp \
  "$here/fp-slice.isail" --lean-real-numbers --lean-noncomputable --lean-single-file

# elaborate.sh with the target Sail copies the translation and lean-sail into REPO_COPY/tmp/sail,
# applies fix-output.sh, and appends the libraries, building only lean-sail.
sh "$here/elaborate.sh" "$repo" "$work/lean-sail" "$work/out/armv9fp" Armv9fp Sail
fixed=$repo/tmp/sail/Armv9fp
{
  hashes "$model" '*.sail' sail-arm
  hashes "$work/lean-sail" '*.lean' lean-sail
  hashes "$work/out/armv9fp" '*' generated
  hashes "$fixed" '*.lean' fixed
} >"$work/hashes.txt"
if [ "$record" = 1 ]; then
  cp "$work/hashes.txt" "$here/check.sha256"
  echo "check.sh: recorded $here/check.sha256"
elif ! diff -u "$here/check.sha256" "$work/hashes.txt"; then
  echo "check.sh: the hashes differ from check.sha256" >&2
  exit 1
else
  echo "check.sh: every hash equals check.sha256"
fi

mkdir -p "$repo/tmp/sail/f7"
cp -R "$here/F7" "$repo/tmp/sail/f7/"
if ! grep -q '^lean_lib F7 where' "$repo/lakefile.lean"; then
  cat >>"$repo/lakefile.lean" <<'EOF'

lean_lib F7 where
  srcDir := "tmp/sail/f7"
  globs := #[.submodules `F7]
  moreLeanArgs := #["--tstack=400000"]
EOF
fi

# axioms LABEL: builds F7, prints the axioms of the theorems of Axioms.lean, and fails on any
# axiom besides propext, Classical.choice, and Quot.sound.
axioms() {
  (cd "$repo" && lake build F7)
  (cd "$repo" && lake env lean --tstack=400000 "$here/Axioms.lean") >"$work/axioms-$1.txt"
  cat "$work/axioms-$1.txt"
  if grep -v "depends on axioms: \[" "$work/axioms-$1.txt" | grep -q .; then
    echo "check.sh: unexpected output ($1)" >&2
    exit 1
  fi
  extra=$(sed 's/.*depends on axioms: \[\(.*\)\]$/\1/' "$work/axioms-$1.txt" | tr ',' '\n' |
    sed 's/^ *//' | grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
  if [ -n "$extra" ]; then
    echo "check.sh: axioms besides propext, Classical.choice, and Quot.sound ($1): $extra" >&2
    exit 1
  fi
  echo "check.sh: axioms checked ($1)"
}

real=$fixed/Armv9fp/Real.lean
cp "$real" "$work/Real.lean"
n=$(grep -c '^def undefined_real (_ : Unit) : SailM real := return default$' "$real" || true)
if [ "$n" != 1 ]; then
  echo "check.sh: $real has $n definitions of undefined_real in the expected form" >&2
  exit 1
fi
sed -i 's/^def undefined_real (_ : Unit) : SailM real := return default$/opaque opaqueReal : real\n\ndef undefined_real (_ : Unit) : SailM real := return opaqueReal/' "$real"
echo "check.sh: undefined_real returns the opaque constant opaqueReal"
axioms opaque
cp "$work/Real.lean" "$real"
echo "check.sh: undefined_real returns default, as generated"
axioms generated
echo "check.sh: passed"
