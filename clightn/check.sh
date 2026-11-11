#!/usr/bin/env bash
# Checks the reference semantics N (clightn/README.md): that the Rocq and the Lean rendering of
# clightn/N.nsx and of the instances of the programs in the table below elaborate to what the
# specification states, that Lean proves every statement and Rocq every statement but the
# instances', which Rocq theorems take as their premises, and that the proofs assume nothing
# beyond CompCert's transf_c_program_correct in Rocq and propext, Classical.choice, and
# Quot.sound in Lean.  The step between the provers assumes the floating-point equations of
# clightn/N.nsx, which the script lists at the end of the comparison.
#
# tools/leanrun builds the Lean modules of the table and runs clightn/emit.lean, which writes each
# program's C text and the bytes of a bare-metal program's output.  The tree's clightgen prints
# each program as a Coq file, from which clightn/clightgen.py writes the instance, and
# clightn/nsx.py renders the instances.  coqc compiles clightn/rocq/*.v, rocq/Clight2Asm.v, the
# Coq files, the renderings of the instances, and a generated NRead.v against a CompCert 3.18 tree
# with built proofs, with the load paths of the tree's _CoqProject; NRead.v prints what Rocq
# elaborated.  Lean compiles the renderings of the instances outside the package and elaborates
# clightn/lean/NAME.lean of each instance, which proves its statement and prints what Lean
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

# The instances: the program's name, which names its files, the Lean module of the theorem that
# the instance carries, which the script builds and clightn/lean/Name.lean imports, the form of
# the instance's statement, and, for a bare-metal program, the result and, when its entry may
# abort, the code of unreachable (clightn/clightgen.py).  clightn/emit.lean writes the C text of
# each program, and the Rocq theorem of the instance is NName.name_asm in clightn/rocq/NName.v.
table='gcd TestSupport.Bare.Gcd terminates 0
crc32 TestSupport.Bare.Theorems terminates 0 1
sha256 TestSupport.Bare.Theorems terminates 0 1
euler TestSupport.Bare.Theorems terminates 0 1
depth TestSupport.Bare.Theorems terminates 0 1
sha TestSupport.Bare.Input reads
ctl TestSupport.Bare.Ctl reacts
echo TestSupport.Bare.Req reacts
deadline TestSupport.Bare.Req reacts
records TestSupport.Bare.Records reacts
gateway Demos.Energy.Loop reacts'
names=()
modules=()
forms=()
args=()
while read -r name module form rest; do
  names+=("$name")
  modules+=("$module")
  forms+=("$form")
  args+=("$rest")
done <<<"$table"

spec=clightn/N.nsx
work=$root/build/clightn
rm -rf "$work"
mkdir -p "$work/rocq" "$work/render" "$work/lean" "$work/planted"
specs=$spec
rocqouts=$work/render/NSpec.v
leanouts=$work/render/Spec.lean
generated=()
proofs=(NBase.v NSpec.v NProof.v Clight2Asm.v NExec.v NExport.v NInst.v)
for n in "${names[@]}"; do
  c=${n^}
  mkdir -p "$work/$n" "$work/lean/ClightN$c"
  specs+=,$work/$n/$c.nsx
  rocqouts+=,$work/$n/N${c}Spec.v
  leanouts+=,$work/lean/ClightN$c/${c}Spec.lean
  generated+=("$work/$n/$n.v" "$work/$n/N${c}Spec.v")
  proofs+=("$n.v" "N${c}Spec.v" "N$c.v")
done

# The Lean proof of the Euler solver's instance takes about 20 minutes and reaches about 33 GB.
leanrun() {
  tools/leanrun --timeout 120m --memory-high 38G "$@"
}

# The programs: their C text, clightgen's Coq files, and the instances.
start=$(date +%s)
mapfile -t built < <(printf '%s\n' "${modules[@]}" | sort -u)
leanrun lake build LeanExe.Native.ClightN.Instance LeanExe.Native.ClightN.Read "${built[@]}" \
  >"$work/build.log" 2>&1 || {
  cat "$work/build.log" >&2
  echo "clightn: the Lean build failed" >&2
  exit 1
}
leanrun lake env lean --run clightn/emit.lean "$work" "${names[@]}" >"$work/emit.log" 2>&1 || {
  cat "$work/emit.log" >&2
  exit 1
}
for i in "${!names[@]}"; do
  n=${names[$i]}
  c=${n^}
  (cd "$work/$n" && "$tree/clightgen" "$n.c")
  if [ "${forms[$i]}" = terminates ]; then
    # shellcheck disable=SC2086
    uv run clightn/clightgen.py "$work/$n/$n.v" "$work/$n/$c.nsx" "$n" "N${c}Spec" \
      "N$c.${n}_asm" terminates "$(cat "$work/$n/$n.bytes")" ${args[$i]}
  else
    uv run clightn/clightgen.py "$work/$n/$n.v" "$work/$n/$c.nsx" "$n" "N${c}Spec" \
      "N$c.${n}_asm" "${forms[$i]}"
  fi
done
uv run clightn/nsx.py render "$specs" "$rocqouts" "$leanouts"
echo "clightn: Lean built and the programs' instances were written in $(($(date +%s) - start)) s"

# rocq OUT BASE READER_FLAG SPECS FILE...: copies the Rocq sources and the generated Rocq files
# into $work/OUT, then the compiled files of $work/rocq when BASE is yes, then the planted files
# of $work/planted/OUT when that directory exists, and compiles FILE... and the reader of SPECS
# there.
rocq() {
  local out=$work/$1 base=$2 reader=$3 rspecs=$4 planted=$work/planted/$1
  shift 4
  mkdir -p "$out"
  cp clightn/rocq/*.v rocq/Clight2Asm.v "${generated[@]}" "$out/"
  if [ "$base" = yes ]; then
    cp "$work"/rocq/*.vo "$out/"
  fi
  if [ -d "$planted" ]; then
    cp "$planted"/*.v "$out/"
  fi
  uv run clightn/nsx.py rocq-reader "$rspecs" "$out/NRead.v" $reader
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
rocq rocq no "" "$specs" "${proofs[@]}"
echo "clightn: Rocq compiled the renderings and proofs in $(($(date +%s) - start)) s"
for n in "${names[@]}"; do
  c=${n^}
  start=$(date +%s)
  leanrun lake env lean -R "$work/lean" -o "$work/lean/ClightN$c/${c}Spec.olean" \
    "$work/lean/ClightN$c/${c}Spec.lean" >"$work/lean/render$c.log" 2>&1 || {
    cat "$work/lean/render$c.log" >&2
    echo "clightn: Lean failed on the rendering of the instance $n" >&2
    exit 1
  }
  lean "clightn/lean/$c.lean" "$work/lean-$n.out"
  echo "clightn: Lean proved the instance $n and printed the renderings and proofs in" \
    "$(($(date +%s) - start)) s"
done
for n in "${names[@]}"; do
  uv run clightn/nsx.py check "$spec,$work/$n/${n^}.nsx" "$work/rocq" "$work/lean-$n.out"
done
uv run clightn/nsx.py equations "$spec"

if [ "$mutations" = yes ]; then
  # The printout of N alone, without an instance, for the checks against N.nsx alone.
  lean clightn/read.lean "$work/lean-n.out"

  # lean_plant GROUP SRC SPECS SCOPE [FORM]: plants the errors of GROUP in a copy of the Lean file
  # SRC, elaborates it, and requires the check against SPECS, of the proofs when SCOPE is proofs,
  # to report exactly those errors.  FORM is the form of an instance's statement.
  lean_plant() {
    local group=$1 src=$2 gspecs=$3 scope=$4 keys
    keys=$(uv run clightn/nsx.py mutate "$group" "$src" "$work/planted/$group.lean" ${5-})
    lean "$work/planted/$group.lean" "$work/planted/$group.out"
    if [ "$scope" = proofs ]; then
      uv run clightn/nsx.py check "$gspecs" "$work/rocq" "$work/planted/$group.out" \
        --expect "$keys"
    else
      uv run clightn/nsx.py check "$gspecs" "$work/rocq" "$work/planted/$group.out" \
        --no-proofs --expect "$keys"
    fi
  }

  # rocq_plant GROUP SRC SPECS LEAN_OUT SCOPE FORM FILE...: plants the errors of GROUP in a copy
  # of the Rocq file SRC, compiles FILE... and the reader, and requires the check against SPECS
  # and the Lean printout LEAN_OUT to report exactly those errors.  SCOPE renderings compiles the
  # renderings and a reader without proofs, proofs compiles N's proofs, and instance compiles an
  # instance's theorem after the compiled files of the first run.
  rocq_plant() {
    local group=$1 src=$2 gspecs=$3 out=$4 scope=$5 form=$6 keys
    shift 6
    mkdir -p "$work/planted/$group"
    keys=$(uv run clightn/nsx.py mutate "$group" "$src" \
      "$work/planted/$group/$(basename "$src")" $form)
    case $scope in
      renderings)
        rocq "$group" no --no-proofs "$gspecs" "$@"
        uv run clightn/nsx.py check "$gspecs" "$work/$group" "$out" --no-proofs \
          --expect "$keys"
        ;;
      proofs)
        rocq "$group" no "" "$gspecs" "$@"
        uv run clightn/nsx.py check "$gspecs" "$work/$group" "$out" --expect "$keys"
        ;;
      instance)
        rocq "$group" yes "" "$gspecs" "$@"
        uv run clightn/nsx.py check "$gspecs" "$work/$group" "$out" --expect "$keys"
        ;;
    esac
  }

  start=$(date +%s)
  lean_plant lean-spec LeanExe/Native/ClightN/Spec.lean "$spec" renderings
  lean_plant lean-proof LeanExe/Native/ClightN/Leaf.lean "$spec" proofs
  rocq_plant rocq-spec clightn/rocq/NSpec.v "$spec" "$work/lean-n.out" renderings "" \
    NBase.v NSpec.v
  rocq_plant rocq-proof clightn/rocq/NProof.v "$spec" "$work/lean-n.out" proofs "" \
    NBase.v NSpec.v NProof.v
  echo "clightn: every error planted in N was reported, in $(($(date +%s) - start)) s"
  for i in "${!names[@]}"; do
    n=${names[$i]}
    c=${n^}
    ispecs=$spec,$work/$n/$c.nsx
    start=$(date +%s)
    lean_plant "lean-$n" "$work/lean/ClightN$c/${c}Spec.lean" "$ispecs" renderings \
      "${forms[$i]}"
    lean_plant "lean-$n-proof" "clightn/lean/$c.lean" "$ispecs" proofs "${forms[$i]}"
    rocq_plant "rocq-$n" "$work/$n/N${c}Spec.v" "$ispecs" "$work/lean-$n.out" renderings \
      "${forms[$i]}" NBase.v NSpec.v "N${c}Spec.v"
    rocq_plant "rocq-$n-proof" "clightn/rocq/N$c.v" "$ispecs" "$work/lean-$n.out" instance \
      "${forms[$i]}" "N$c.v"
    echo "clightn: every error planted in the instance $n was reported, in" \
      "$(($(date +%s) - start)) s"
  done
  echo "clightn: every planted error was reported"
fi
