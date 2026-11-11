#!/usr/bin/env bash
# Checks the reference semantics N (clightn/README.md): that the Rocq and the Lean rendering of
# clightn/N.nsx and of the instances of two programs elaborate to what the specification states,
# that Lean proves every statement and Rocq every statement but the instances', which Rocq
# theorems take as their premises, and that the proofs assume nothing beyond CompCert's
# transf_c_program_correct in Rocq and propext, Classical.choice, and Quot.sound in Lean.
#
# The instances are the bare-metal program of gcd 1071 462 and the program with input around the
# export sha256 of the hashing library.  tools/leanrun builds the Lean modules and runs
# clightn/gcd/emit.lean and clightn/sha/emit.lean, which write the programs' C text and the bytes
# of the GCD program's output.  The tree's clightgen prints each program as a Coq file, from which
# clightn/clightgen.py writes the instances Gcd.nsx and Sha.nsx, and clightn/nsx.py renders them.
# coqc compiles clightn/rocq/*.v, rocq/Clight2Asm.v, the Coq files, the renderings of the
# instances, and a generated NRead.v against a CompCert 3.18 tree with built proofs, with the
# load paths of the tree's _CoqProject; NRead.v prints what Rocq elaborated.  Lean compiles the
# renderings of the instances outside the package and elaborates clightn/gcd/Gcd.lean and
# clightn/sha/Sha.lean, each of which proves its instance's statement and prints what Lean
# elaborated.  clightn/nsx.py compares the printouts with the specification, once for each
# instance.  With --mutations, the script then plants the errors that nsx.py lists in copies of
# the renderings and the proofs, and requires the comparison to report exactly those errors.  Its
# work directory is build/clightn.
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
mkdir -p "$work/rocq" "$work/gcd" "$work/sha" "$work/lean/ClightNGcd" "$work/lean/ClightNSha" \
  "$work/render"
gcdspecs=$spec,$work/gcd/Gcd.nsx
shaspecs=$spec,$work/sha/Sha.nsx
specs=$spec,$work/gcd/Gcd.nsx,$work/sha/Sha.nsx
proofs=(NBase.v NSpec.v NProof.v Clight2Asm.v NExec.v NExport.v gcd.v NGcdSpec.v NGcd.v sha.v
  NShaSpec.v NSha.v)

# The Lean proof of the SHA-256 instance reaches about 12 GB, of which the imports take about 4 GB.
leanrun() {
  tools/leanrun --timeout 60m --memory-high 14G "$@"
}

# The programs: their C text, clightgen's Coq files, and the instances.
start=$(date +%s)
leanrun lake build LeanExe.Native.ClightN.Instance LeanExe.Native.ClightN.Read \
  TestSupport.Bare.Gcd TestSupport.Bare.Input >"$work/build.log" 2>&1 || {
  cat "$work/build.log" >&2
  echo "clightn: the Lean build failed" >&2
  exit 1
}
for p in gcd sha; do
  leanrun lake env lean --run "clightn/$p/emit.lean" "$work/$p" >"$work/$p/emit.log" 2>&1 || {
    cat "$work/$p/emit.log" >&2
    exit 1
  }
  (cd "$work/$p" && "$tree/clightgen" "$p.c")
done
uv run clightn/clightgen.py "$work/gcd/gcd.v" "$work/gcd/Gcd.nsx" gcd NGcdSpec NGcd.gcd_asm \
  terminates "$(cat "$work/gcd/gcd.bytes")" 0
uv run clightn/clightgen.py "$work/sha/sha.v" "$work/sha/Sha.nsx" sha NShaSpec NSha.sha_asm reads
uv run clightn/nsx.py render "$specs" \
  "$work/render/NSpec.v,$work/gcd/NGcdSpec.v,$work/sha/NShaSpec.v" \
  "$work/render/Spec.lean,$work/lean/ClightNGcd/GcdSpec.lean,$work/lean/ClightNSha/ShaSpec.lean"
echo "clightn: Lean built and the programs' instances were written in $(($(date +%s) - start)) s"

# rocq DIR READER_FLAG FILE...: compiles the Rocq files from DIR (the repository's files unless
# DIR holds a planted copy) and the reader into $work/DIR's name.
rocq() {
  local dir=$1 reader=$2 out=$work/$3
  shift 3
  mkdir -p "$out"
  cp clightn/rocq/*.v rocq/Clight2Asm.v "$work/gcd/gcd.v" "$work/gcd/NGcdSpec.v" \
    "$work/sha/sha.v" "$work/sha/NShaSpec.v" "$out/"
  if [ -n "$dir" ]; then
    cp "$dir"/*.v "$out/"
  fi
  uv run clightn/nsx.py rocq-reader "${SPECS:-$specs}" "$out/NRead.v" $reader
  (cd "$out" && for f in "$@" NRead.v; do coqc "${flags[@]}" "$f" >/dev/null; done)
}

# lean FILE OUT: elaborates FILE, which runs the reader, with the reader's output in OUT and the
# compiled renderings of the instances on the load path.
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
for x in Gcd Sha; do
  leanrun lake env lean -R "$work/lean" -o "$work/lean/ClightN$x/${x}Spec.olean" \
    "$work/lean/ClightN$x/${x}Spec.lean" >"$work/lean/render$x.log" 2>&1 || {
    cat "$work/lean/render$x.log" >&2
    echo "clightn: Lean failed on the rendering of the $x instance" >&2
    exit 1
  }
done
lean clightn/gcd/Gcd.lean "$work/lean-gcd.out"
echo "clightn: Lean proved the GCD instance and printed the renderings and proofs in" \
  "$(($(date +%s) - start)) s"
start=$(date +%s)
lean clightn/sha/Sha.lean "$work/lean-sha.out"
echo "clightn: Lean proved the SHA-256 instance and printed the renderings and proofs in" \
  "$(($(date +%s) - start)) s"
uv run clightn/nsx.py check "$gcdspecs" "$work/rocq" "$work/lean-gcd.out"
uv run clightn/nsx.py check "$shaspecs" "$work/rocq" "$work/lean-sha.out"

if [ "$mutations" = yes ]; then
  mkdir -p "$work/planted"
  # The printout of N alone, without an instance, for the checks against N.nsx alone.
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
lean-gcd $work/lean/ClightNGcd/GcdSpec.lean $gcdspecs renderings
lean-sha $work/lean/ClightNSha/ShaSpec.lean $shaspecs renderings
lean-proof LeanExe/Native/ClightN/Leaf.lean $spec proofs
lean-gcd-proof clightn/gcd/Gcd.lean $gcdspecs proofs
lean-sha-proof clightn/sha/Sha.lean $shaspecs proofs
EOF
  # Each line: the group, the file it plants errors in, the specification files of the check,
  # the Lean printout to compare with, and the files that Rocq compiles before the reader; the
  # reader covers the proofs when it compiles them.
  while read -r group src specfiles out files; do
    mkdir -p "$work/planted/$group"
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
rocq-spec clightn/rocq/NSpec.v $spec $work/lean-n.out NBase.v,NSpec.v
rocq-gcd $work/gcd/NGcdSpec.v $gcdspecs $work/lean-gcd.out NBase.v,NSpec.v,NGcdSpec.v
rocq-sha $work/sha/NShaSpec.v $shaspecs $work/lean-sha.out NBase.v,NSpec.v,NShaSpec.v
rocq-proof clightn/rocq/NProof.v $spec $work/lean-n.out proofs
rocq-gcd-proof clightn/rocq/NGcd.v $gcdspecs $work/lean-gcd.out all
rocq-sha-proof clightn/rocq/NSha.v $shaspecs $work/lean-sha.out all
EOF
  echo "clightn: every planted error was reported"
fi
