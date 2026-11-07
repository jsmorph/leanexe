#!/usr/bin/env bash
# Compares the Rocq evaluator of rocq/ClightEval.v, which is sound for CompCert's big-step
# semantics of Clight, with LClight.run on the programs that tests/native/clight.sh writes.  DIR
# holds C programs with their .expected files, as clight.sh leaves them under
# build/native/clight/SEED, and TREE is a CompCert 3.18 tree whose proofs are built, configured
# for the target of the Archi instance that computed the .expected files.  clightgen prints each
# program as Clight in Coq, and coqc checks for each program a lemma, proved by vm_compute, that
# the output of rocq/ClightPrint.v equals the lines of its .expected file: test_output for the
# random programs t* and the NaN programs nan*, and trace_output for the trace programs v* and
# the input programs w*.  coqc checks BATCH programs per file, 10 unless the caller sets it, and
# JOBS files at a time, the number of processors unless the caller sets it.  When a file fails,
# coqc checks each of its programs alone, and a program whose check fails is reported with the
# difference between the expected lines and those that the evaluator computes, or with coqc's
# error when the two do not differ.  A program whose expected output is FUEL is counted and
# skipped.
# Usage: tests/native/clight-rocq.sh DIR TREE
set -euo pipefail
if [ "$#" -ne 2 ]; then
  echo "usage: tests/native/clight-rocq.sh DIR TREE" >&2
  exit 2
fi
dir=$(cd "$1" && pwd)
tree=$(cd "$2" && pwd)
root=$(cd "$(dirname "$0")/../.." && pwd)
batch=${BATCH:-10}
jobs=${JOBS:-$(nproc)}
if [ ! -f "$tree/_CoqProject" ] || [ ! -x "$tree/clightgen" ] ||
  [ ! -f "$tree/cfrontend/ClightBigstep.vo" ] || [ ! -f "$tree/export/Clightdefs.vo" ]; then
  echo "clight-rocq: $tree is not a CompCert tree with built proofs and clightgen" >&2
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
cp "$root/rocq/ClightEval.v" "$root/rocq/ClightPrint.v" "$work/"
(cd "$work" && coqc "${flags[@]}" ClightEval.v && coqc "${flags[@]}" ClightPrint.v)
mkdir "$work/src"

pass=0
undefined=0
fuel=0
fail=0
traces=0
inputs=0
names=()
for c in "$dir"/t*.c "$dir"/nan*.c "$dir"/v*.c "$dir"/w*.c; do
  name=$(basename "$c" .c)
  if [ "$(cat "$dir/$name.expected")" = "FUEL" ]; then
    fuel=$((fuel + 1))
    continue
  fi
  cp "$c" "$work/src/"
  names+=("$name")
done
printf '%s.c\n' "${names[@]}" | (cd "$work/src" &&
  xargs -P "$jobs" -I{} sh -c '"$1" "$2" >"$2.log" 2>&1 || touch "$2.failed"' \
    sh "$tree/clightgen" {})

output_of() {
  case $1 in
    v* | w*) echo trace_output ;;
    *) echo test_output ;;
  esac
}

header() {
  echo "From Coq Require Import String List ZArith."
  echo "From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs."
  echo "Require ClightPrint."
}

# The Clight program of NAME, which clightgen printed, in the module NAME.
module_text() {
  echo "Module $1."
  grep -v '^From \|^Require ' "$work/src/$1.v"
  echo "End $1."
}

# The lemma that the output of the evaluator for NAME is the expected one.
lemma_text() {
  echo "Lemma ${1}_agrees : ClightPrint.$(output_of "$1") $1.prog ="
  awk '{ gsub(/"/, "\"\""); printf "  \"%s\"%%string ::\n", $0 } END { print "  nil." }' \
    "$dir/$1.expected"
  echo "Proof. vm_compute. reflexivity. Qed."
}

# Checks FILE.v with coqc and records the result in FILE.status.
check() {
  if (cd "$work" && coqc "${flags[@]}" "$1.v" >"$1.out" 2>&1); then
    echo pass >"$work/$1.status"
  else
    echo fail >"$work/$1.status"
  fi
}

# Runs check on each argument, JOBS at a time.
check_all() {
  local running=0 f
  for f in "$@"; do
    check "$f" &
    running=$((running + 1))
    if [ "$running" -ge "$jobs" ]; then
      wait -n
      running=$((running - 1))
    fi
  done
  wait
}

generated=()
for name in "${names[@]}"; do
  if [ ! -f "$work/src/$name.c.failed" ]; then
    generated+=("$name")
  fi
done
batches=()
for ((k = 0; k * batch < ${#generated[@]}; k++)); do
  {
    header
    for name in "${generated[@]:k*batch:batch}"; do
      module_text "$name"
      lemma_text "$name"
    done
  } >"$work/batch$k.v"
  printf '%s\n' "${generated[@]:k*batch:batch}" >"$work/batch$k.names"
  batches+=("batch$k")
done
check_all "${batches[@]}"

single=()
for b in "${batches[@]}"; do
  if [ "$(cat "$work/$b.status")" = fail ]; then
    while read -r name; do
      { header; module_text "$name"; lemma_text "$name"; } >"$work/single_$name.v"
      single+=("single_$name")
    done <"$work/$b.names"
  fi
done
if [ "${#single[@]}" -gt 0 ]; then
  check_all "${single[@]}"
fi

for name in "${names[@]}"; do
  if [ -f "$work/src/$name.c.failed" ]; then
    echo "fail: $name: clightgen failed" >&2
    cat "$work/src/$name.c.log" >&2
    fail=$((fail + 1))
    continue
  fi
  if [ -f "$work/single_$name.status" ] && [ "$(cat "$work/single_$name.status")" = fail ]; then
    echo "fail: $name" >&2
    {
      header
      echo "Import ListNotations."
      echo "Open Scope string_scope."
      module_text "$name"
      echo "Eval vm_compute in ClightPrint.$(output_of "$name") $name.prog."
    } >"$work/show_$name.v"
    if (cd "$work" && coqc "${flags[@]}" "show_$name.v" >"show_$name.out" 2>/dev/null) &&
      ! diff "$dir/$name.expected" <(grep -o '"[^"]*"' "$work/show_$name.out" |
        sed 's/^"//; s/"$//') >&2; then
      :
    else
      echo "coqc failed:" >&2
      cat "$work/single_$name.out" >&2
    fi
    fail=$((fail + 1))
    continue
  fi
  pass=$((pass + 1))
  case $name in
    v*) traces=$((traces + 1)) ;;
    w*) inputs=$((inputs + 1)) ;;
  esac
  if [ "$(cat "$dir/$name.expected")" = UB ]; then
    undefined=$((undefined + 1))
  fi
done
echo "clight-rocq: $pass agree ($undefined undefined, $traces trace programs, $inputs input programs), $fail differ, $fuel out of fuel"
[ "$fail" -eq 0 ]
