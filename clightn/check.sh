#!/usr/bin/env bash
# Checks the reference semantics N (clightn/README.md): that the Rocq and the Lean rendering of
# clightn/N.nsx and of the instance of the GCD program elaborate to what the specification states,
# that Lean proves every statement and Rocq every statement but the GCD program's, which a Rocq
# theorem takes as its premise, and that the proofs assume nothing beyond CompCert's
# transf_c_program_correct in Rocq and propext, Classical.choice, and Quot.sound in Lean.
#
# tools/leanrun builds the Lean modules and runs clightn/gcd/emit.lean, which writes the C text of
# the bare-metal program of gcd 1071 462 and the bytes of its output.  The tree's clightgen prints
# the program as a Coq file, from which clightn/clightgen.py writes the instance Gcd.nsx, and
# clightn/nsx.py renders it.  coqc compiles clightn/rocq/*.v, the Coq file, the rendering of the
# instance, rocq/Clight2Asm.v, and a generated NRead.v against a CompCert 3.18 tree with built
# proofs, with the load paths of the tree's _CoqProject; NRead.v prints what Rocq elaborated.
# Lean compiles the rendering of the instance outside the package and elaborates
# clightn/gcd/Gcd.lean, which proves the instance's statement and prints what Lean elaborated.
# clightn/nsx.py compares both printouts with the specification.  With --mutations, the script then
# plants the errors that nsx.py lists in copies of the renderings and the proofs, and requires the
# comparison to report exactly those errors.  Its work directory is build/clightn.
# Usage: clightn/check.sh [--mutations] COMPCERT_TREE
set -euo pipefail
mutations=no
if [ "${1-}" = --mutations ]; then
  mutations=yes
  shift
fi
if [ "$#" -ne 1 ]; then
  echo "usage: clightn/check.sh [--mutations] COMPCERT_TREE" >&2
  exit 2
fi
tree=$(cd "$1" && pwd)
root=$(cd "$(dirname "$0")/.." && pwd)
if [ ! -f "$tree/_CoqProject" ] || [ ! -f "$tree/driver/Compiler.vo" ] ||
    [ ! -x "$tree/clightgen" ]; then
  echo "clightn: $tree is not a CompCert tree with built proofs and clightgen" >&2
  exit 2
fi
arch=$(sed -n 's/^ARCH=//p' "$tree/Makefile.config")
if [ "$arch" != aarch64 ]; then
  echo "clightn: N describes AArch64, and $tree is configured for ${arch:-no architecture}" >&2
  exit 2
fi
read -ra words <<<"$(tr '\n' ' ' <"$tree/_CoqProject")"
flags=()
i=0
while [ "$i" -lt "${#words[@]}" ]; do
  if [ "${words[$i]}" = "-R" ]; then
    flags+=(-R "$tree/${words[$((i + 1))]}" "${words[$((i + 2))]}")
    i=$((i + 3))
  else
    flags+=("${words[$i]}")
    i=$((i + 1))
  fi
done
flags+=(-Q . "")
cd "$root"
spec=clightn/N.nsx
work=$root/build/clightn
rm -rf "$work"
mkdir -p "$work/rocq" "$work/gcd" "$work/lean/ClightNGcd" "$work/render"
specs=$spec,$work/gcd/Gcd.nsx
proofs=(NBase.v NSpec.v NProof.v NExec.v NExport.v gcd.v NGcdSpec.v Clight2Asm.v NGcd.v)

# The Lean proof of the GCD instance reaches about 6 GB, of which the imports take about 4 GB.
leanrun() {
  tools/leanrun --timeout 45m --memory-high 10G "$@"
}

# The GCD program: its C text, clightgen's Coq file, and the instance.
start=$(date +%s)
leanrun lake build LeanExe.Native.ClightN.Exec LeanExe.Native.ClightN.Read TestSupport.Bare.Gcd \
  >"$work/build.log" 2>&1 || {
  cat "$work/build.log" >&2
  echo "clightn: the Lean build failed" >&2
  exit 1
}
leanrun lake env lean --run clightn/gcd/emit.lean "$work/gcd" >"$work/gcd/emit.log" 2>&1 || {
  cat "$work/gcd/emit.log" >&2
  exit 1
}
(cd "$work/gcd" && "$tree/clightgen" gcd.c)
uv run clightn/clightgen.py "$work/gcd/gcd.v" "$work/gcd/Gcd.nsx" gcd NGcdSpec NGcd.gcd_asm \
  "$(cat "$work/gcd/gcd.bytes")" 0
uv run clightn/nsx.py render "$specs" "$work/render/NSpec.v,$work/gcd/NGcdSpec.v" \
  "$work/render/Spec.lean,$work/lean/ClightNGcd/GcdSpec.lean"
echo "clightn: Lean built and the GCD program's instance was written in $(($(date +%s) - start)) s"

# rocq DIR READER_FLAG FILE...: compiles the Rocq files from DIR (the repository's files unless
# DIR holds a planted copy) and the reader into $work/DIR's name.
rocq() {
  local dir=$1 reader=$2 out=$work/$3
  shift 3
  mkdir -p "$out"
  cp clightn/rocq/*.v rocq/Clight2Asm.v "$work/gcd/gcd.v" "$work/gcd/NGcdSpec.v" "$out/"
  if [ -n "$dir" ]; then
    cp "$dir"/*.v "$out/"
  fi
  uv run clightn/nsx.py rocq-reader "${SPECS:-$specs}" "$out/NRead.v" $reader
  (cd "$out" && for f in "$@" NRead.v; do coqc "${flags[@]}" "$f" >/dev/null; done)
}

# lean FILE OUT: elaborates FILE, which runs the reader, with the reader's output in OUT and the
# compiled rendering of the GCD instance on the load path.
lean() {
  CLIGHTN_OUT=$2 GEN=$work/lean leanrun lake env sh -c \
    'LEAN_PATH="$LEAN_PATH:$GEN" exec lean "$0"' "$1" >"$2.log" 2>&1 || {
    cat "$2.log" >&2
    echo "clightn: Lean failed on $1" >&2
    exit 1
  }
}

start=$(date +%s)
rocq "" "" rocq "${proofs[@]}"
echo "clightn: Rocq compiled the renderings and proofs in $(($(date +%s) - start)) s"
start=$(date +%s)
leanrun lake env lean -R "$work/lean" -o "$work/lean/ClightNGcd/GcdSpec.olean" \
  "$work/lean/ClightNGcd/GcdSpec.lean" >"$work/lean/render.log" 2>&1 || {
  cat "$work/lean/render.log" >&2
  echo "clightn: Lean failed on the rendering of the GCD instance" >&2
  exit 1
}
lean clightn/gcd/Gcd.lean "$work/lean.out"
echo "clightn: Lean proved the GCD instance and printed the renderings and proofs in" \
  "$(($(date +%s) - start)) s"
uv run clightn/nsx.py check "$specs" "$work/rocq" "$work/lean.out"

if [ "$mutations" = yes ]; then
  mkdir -p "$work/planted"
  # The printout of N alone, without the GCD instance, for the checks against N.nsx alone.
  lean clightn/read.lean "$work/lean-n.out"
  # Each line: the group, the file it plants errors in, the specification files of the check,
  # and whether the check covers the proofs.
  while read -r group src specfiles scope; do
    keys=$(uv run clightn/nsx.py mutate "$group" "$src" "$work/planted/$group.lean")
    lean "$work/planted/$group.lean" "$work/planted/$group.out"
    if [ "$scope" = proofs ]; then
      uv run clightn/nsx.py check "$specfiles" "$work/rocq" "$work/planted/$group.out" \
        --expect "$keys"
    else
      uv run clightn/nsx.py check "$specfiles" "$work/rocq" "$work/planted/$group.out" \
        --no-proofs --expect "$keys"
    fi
  done <<EOF
lean-spec LeanExe/Native/ClightN/Spec.lean $spec renderings
lean-gcd $work/lean/ClightNGcd/GcdSpec.lean $specs renderings
lean-proof LeanExe/Native/ClightN/Leaf.lean $spec proofs
lean-gcd-proof clightn/gcd/Gcd.lean $specs proofs
EOF
  # Each line: the group, the file it plants errors in, the specification files of the check,
  # and the files that Rocq compiles before the reader; the reader covers the proofs when it
  # compiles them.
  while read -r group src specfiles files; do
    mkdir -p "$work/planted/$group"
    out=$work/lean.out
    if [ "$specfiles" = "$spec" ]; then
      out=$work/lean-n.out
    fi
    keys=$(uv run clightn/nsx.py mutate "$group" "$src" "$work/planted/$group/$(basename "$src")")
    if [ "$files" = all ]; then
      SPECS=$specfiles rocq "$work/planted/$group" "" "$group" "${proofs[@]}"
      uv run clightn/nsx.py check "$specfiles" "$work/$group" "$out" --expect "$keys"
    elif [ "$files" = proofs ]; then
      SPECS=$specfiles rocq "$work/planted/$group" "" "$group" NBase.v NSpec.v NProof.v
      uv run clightn/nsx.py check "$specfiles" "$work/$group" "$out" --expect "$keys"
    else
      SPECS=$specfiles rocq "$work/planted/$group" --no-proofs "$group" ${files//,/ }
      uv run clightn/nsx.py check "$specfiles" "$work/$group" "$out" --no-proofs \
        --expect "$keys"
    fi
  done <<EOF
rocq-spec clightn/rocq/NSpec.v $spec NBase.v,NSpec.v
rocq-gcd $work/gcd/NGcdSpec.v $specs NBase.v,NSpec.v,NGcdSpec.v
rocq-proof clightn/rocq/NProof.v $spec proofs
rocq-gcd-proof clightn/rocq/NGcd.v $specs all
EOF
  echo "clightn: every planted error was reported"
fi
