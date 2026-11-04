#!/usr/bin/env bash
# Checks the Rocq files of this directory against a CompCert 3.18 tree whose proofs are built,
# outside the default build (docs/native-bare-metal.md).  coqc compiles Clight2Asm.v and
# ClightEval.v in a temporary directory with the load paths of the tree's _CoqProject, and the
# axioms and parameters that their theorems depend on, by Print Assumptions, must be those of
# CompCert's transf_c_program_correct and, for Clight2Asm.v,
# ClassicalEpsilon.constructive_indefinite_description, which
# forward_simulation_same_safe_behavior of common/Behaviors.v uses.  Clight2Asm.v imports
# Compopts and Events, so the comparison drops those modules' qualifiers.
# Usage: rocq/check.sh COMPCERT_TREE
set -euo pipefail
if [ "$#" -ne 1 ]; then
  echo "usage: rocq/check.sh COMPCERT_TREE" >&2
  exit 2
fi
tree=$(cd "$1" && pwd)
here=$(cd "$(dirname "$0")" && pwd)
if [ ! -f "$tree/_CoqProject" ] || [ ! -f "$tree/driver/Compiler.vo" ]; then
  echo "rocq: $tree is not a CompCert tree with built proofs" >&2
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
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp "$here/Clight2Asm.v" "$here/ClightEval.v" "$work/"
printf 'Require Import Compiler.\nPrint Assumptions transf_c_program_correct.\n' \
  >"$work/Reference.v"
{
  echo 'Require ClightEval.'
  printf 'Print Assumptions ClightEval.%s.\n' exec_call_sound run_sound run_program_sound
} >"$work/Eval.v"
(cd "$work" && coqc "${flags[@]}" Clight2Asm.v >clight2asm.out)
(cd "$work" && coqc "${flags[@]}" ClightEval.v && coqc "${flags[@]}" Eval.v >eval.out)
(cd "$work" && coqc "${flags[@]}" Reference.v >reference.out)
names() {
  grep -oE '^[A-Za-z][A-Za-z0-9_.]*( :|$)' "$1" | sed 's/ :$//; s/^Compopts\.//; s/^Events\.//' | sort -u
}
extra=$(comm -23 <(names "$work/clight2asm.out") <(names "$work/reference.out") | paste -sd' ')
if [ "$extra" != "ClassicalEpsilon.constructive_indefinite_description" ]; then
  echo "rocq: Clight2Asm.v depends on assumptions beyond CompCert's: $extra" >&2
  exit 1
fi
echo "rocq: Clight2Asm.v checks, with the assumptions of transf_c_program_correct and $extra"
extra=$(comm -23 <(names "$work/eval.out") <(names "$work/reference.out") | paste -sd' ')
if [ -n "$extra" ]; then
  echo "rocq: ClightEval.v depends on assumptions beyond CompCert's: $extra" >&2
  exit 1
fi
echo "rocq: ClightEval.v checks, with assumptions among those of transf_c_program_correct"
