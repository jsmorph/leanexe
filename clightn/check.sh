#!/usr/bin/env bash
# Checks the reference semantics N (clightn/README.md): that the Rocq and the Lean rendering of
# clightn/N.nsx elaborate to what the specification states, that each prover proves every
# statement under its name, and that the proofs assume nothing beyond CompCert's
# transf_c_program_correct in Rocq and propext, Classical.choice, and Quot.sound in Lean.  coqc
# compiles clightn/rocq/NBase.v, NSpec.v, and NProof.v and a generated NRead.v against a CompCert
# 3.18 tree with built proofs, with the load paths of the tree's _CoqProject; NRead.v prints what
# Rocq elaborated.  tools/leanrun builds the modules LeanExe.Native.ClightN.* and runs
# clightn/read.lean, which prints what Lean elaborated.  clightn/nsx.py compares both printouts
# with the specification.  With --mutations, the script then plants the errors that nsx.py lists
# in copies of the renderings and the proofs, and requires the comparison to report exactly
# those errors.  Its work directory is build/clightn.
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
if [ ! -f "$tree/_CoqProject" ] || [ ! -f "$tree/driver/Compiler.vo" ]; then
  echo "clightn: $tree is not a CompCert tree with built proofs" >&2
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
mkdir -p "$work/rocq"

# rocq DIR READER_FLAG FILE...: compiles NBase.v, NSpec.v, and NProof.v from DIR (the
# repository's files unless DIR holds a planted copy) and the reader into $work/DIR's name.
rocq() {
  local dir=$1 reader=$2 out=$work/$3
  shift 3
  mkdir -p "$out"
  cp clightn/rocq/NBase.v clightn/rocq/NSpec.v clightn/rocq/NProof.v "$out/"
  if [ -n "$dir" ]; then
    cp "$dir"/*.v "$out/"
  fi
  uv run clightn/nsx.py rocq-reader "$spec" "$out/NRead.v" $reader
  (cd "$out" && for f in "$@" NRead.v; do coqc "${flags[@]}" "$f" >/dev/null; done)
}

# lean FILE OUT: elaborates FILE, which runs the reader, with the reader's output in OUT.
lean() {
  CLIGHTN_OUT=$2 tools/leanrun --timeout 30m lake env lean "$1" >"$2.log" 2>&1 || {
    cat "$2.log" >&2
    echo "clightn: Lean failed on $1" >&2
    exit 1
  }
}

start=$(date +%s)
rocq "" "" rocq NBase.v NSpec.v NProof.v
echo "clightn: Rocq compiled the renderings and proofs in $(($(date +%s) - start)) s"
start=$(date +%s)
tools/leanrun --timeout 30m lake build LeanExe.Native.ClightN.Leaf LeanExe.Native.ClightN.Read \
  >"$work/build.log" 2>&1 || {
  cat "$work/build.log" >&2
  echo "clightn: the Lean build failed" >&2
  exit 1
}
lean clightn/read.lean "$work/lean.out"
echo "clightn: Lean built and printed the renderings and proofs in $(($(date +%s) - start)) s"
uv run clightn/nsx.py check "$spec" "$work/rocq" "$work/lean.out"

if [ "$mutations" = yes ]; then
  mkdir -p "$work/planted"
  keys=$(uv run clightn/nsx.py mutate lean-spec LeanExe/Native/ClightN/Spec.lean \
    "$work/planted/Spec.lean")
  lean "$work/planted/Spec.lean" "$work/planted/lean-spec.out"
  uv run clightn/nsx.py check "$spec" "$work/rocq" "$work/planted/lean-spec.out" --no-proofs \
    --expect "$keys"
  mkdir -p "$work/planted/rocq-spec"
  keys=$(uv run clightn/nsx.py mutate rocq-spec clightn/rocq/NSpec.v \
    "$work/planted/rocq-spec/NSpec.v")
  rocq "$work/planted/rocq-spec" --no-proofs rocq-spec NBase.v NSpec.v
  uv run clightn/nsx.py check "$spec" "$work/rocq-spec" "$work/lean.out" --no-proofs \
    --expect "$keys"
  keys=$(uv run clightn/nsx.py mutate lean-proof LeanExe/Native/ClightN/Leaf.lean \
    "$work/planted/Leaf.lean")
  lean "$work/planted/Leaf.lean" "$work/planted/lean-proof.out"
  uv run clightn/nsx.py check "$spec" "$work/rocq" "$work/planted/lean-proof.out" \
    --expect "$keys"
  mkdir -p "$work/planted/rocq-proof"
  keys=$(uv run clightn/nsx.py mutate rocq-proof clightn/rocq/NProof.v \
    "$work/planted/rocq-proof/NProof.v")
  rocq "$work/planted/rocq-proof" "" rocq-proof NBase.v NSpec.v NProof.v
  uv run clightn/nsx.py check "$spec" "$work/rocq-proof" "$work/lean.out" --expect "$keys"
  echo "clightn: every planted error was reported"
fi
