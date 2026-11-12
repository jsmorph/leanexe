#!/usr/bin/env bash
# Writes the modules of the verified compiler's examples, validates them with wasm-tools, and
# compares their checked cases between the Wasmtime host and native Lean.
# A case with a sixth field also checks the allocation counters: the blocks allocated less those
# released must equal the field, the result's arrays and the host's arrays at borrowed parameters.
# A seventh field bounds the number of allocations, the host's included.  A case whose expected
# result is `trap` must trap at `unreachable`.  After writing the modules, it builds each function's
# theorem module and checks its file theorem module, whose theorems state that the written file
# holds the module of the function's byte theorem, and it fails unless both file theorems report
# only the axioms propext, Classical.choice, and Quot.sound.  For the slew planner, it also compares
# the edgeOk export with native Lean and runs the axiom audit of tests/slew/Axioms.lean, and with
# --cases slew it checks the planner's file theorem module as well.  For the energy authorizer, it
# runs the axiom audit of tests/energy/Axioms.lean, and with --cases energy it checks the
# authorizer's file theorem module as well.  For the conjunction program, it runs the axiom audit
# of tests/conjunction/Axioms.lean, and with --cases conjunction it checks the program's file
# theorem module as well.  For the CE and LE program, it runs the axiom audit of
# tests/conjunction/AccuracyAxioms.lean, and with --cases accuracy it checks the program's file
# theorem module as well, and for the program with adaptive panels it does the same with
# tests/conjunction/AdaptiveAxioms.lean and --cases adaptive.  For the attitude program, it runs the axiom audit of
# tests/attitude/Axioms.lean, and with --cases attitude it checks the program's file theorem module
# as well.  For the chi-square programs, the gate, and the assignment check, it runs the axiom
# audits of tests/gate/ChiSquareAxioms.lean, GateAxioms.lean, and AssignmentAxioms.lean, and with
# --cases chisquare, gate, or assignment it checks that module's file theorems as well.  For the
# q-method, it runs the axiom audit of tests/attitude/QAxioms.lean, and with --cases qmethod it
# checks the q-method's file theorem module as well.  For the SGP4 program, it runs the axiom
# audit of
# tests/sgp4/Axioms.lean, and with --cases sgp4 it checks the program's file theorem module as
# well.  With --cases sgp4box or --cases sgp4omm, it runs the axiom audit of
# tests/sgp4/BoxAxioms.lean or tests/sgp4/OmmAxioms.lean for the enclosing SGP4 program or the
# reader of decimal values and checks that module's file theorems.  For the passive-safety check,
# it runs the axiom audit of tests/passivesafety/Axioms.lean, and with --cases passivesafety it
# checks the check's file theorem module as well.  For the orbit-determination programs, it runs
# the axiom audit of tests/orbit/Axioms.lean, and with --cases gibbs or --cases lambert it checks
# that module's file theorems.  For the screening program, it runs the axiom audit of
# tests/screening/Axioms.lean, and with --cases screening it checks the program's file theorem
# module as well.  For the event-window program, it runs the axiom audit of
# tests/events/Axioms.lean, and with --cases events it checks the program's file theorem module
# as well.  With --cases frames, it runs the axiom audit of tests/frames/Axioms.lean and
# checks the frames module's file theorems, and with --cases geolocation it does the same with
# tests/geolocation/Axioms.lean and the geolocation module.  For the avoidance authorizer, it runs
# the axiom audit of tests/avoidance/Axioms.lean, and with --cases avoidance it checks the
# authorizer's file theorem module as well.  Each audit fails the run when a report names an
# axiom beyond those three.  Last, the
# tests/TestSupport/Numerics/*Accuracy.lean checks compare the transcendental functions with
# references computed with Lean's integers, each within the bound its docstring states, and
# tests/TestSupport/Numerics/FourierAccuracy.lean checks that Fourier.dft, inverse, and
# powerSpectrum behave as their mathematical counterparts.
# Before it loads any module, the script builds every module that it and the scripts it calls load
# and the case executable it runs, in one `lake build` under tools/leanrun with the caller's
# LEANRUN_THREADS and LEANRUN_MEMORY_HIGH, since `lean` and `lean --run` read a module's compiled
# file without checking it against the source.  Building the numerical proofs that need much
# memory and `Verified Library` first, with the limits of docs/verified-manual.md, keeps that
# build within the caller's memory limit.  The build passes `-R` to Lake, which elaborates the Lake
# configuration again in the mode of this run, whichever mode the checkout had.
# With --fast, Lake builds this package's modules with debug.skipKernelTC into .lake/build-fast, so
# the kernel checks none of their proofs, decide +kernel included, the file theorem checks do not
# run, and the script restores the checked configuration when it exits.
# The script records each check that passes with the hash of its inputs in build/verified-checks/,
# in a directory for each mode, and skips a check whose inputs still have the recorded hash.
# --no-cache runs every check.  docs/verified-manual.md#recorded-checks lists the inputs.
# Usage: tests/verified/run.sh [--fast] [--no-cache] [--cases MODULE | --check-bytes DIRECTORY]
set -euo pipefail
shopt -s inherit_errexit
usage() {
  echo "usage: tests/verified/run.sh [--fast] [--no-cache]" \
    "[--cases MODULE | --check-bytes DIRECTORY]" >&2
  exit 2
}
if ! command -v wasm-tools > /dev/null 2>&1; then
  echo "fail: wasm-tools is not on the search path" >&2
  exit 1
fi
case_module=""
reference=""
fast=0
cache=1
while [ "$#" -ne 0 ]; do
  case "$1" in
    --fast) fast=1; shift ;;
    --no-cache) cache=0; shift ;;
    --cases | --check-bytes)
      if [ "$#" -lt 2 ] || [ -z "$2" ] || [ -n "$case_module$reference" ]; then usage; fi
      if [ "$1" = "--cases" ]; then case_module=$2; else reference=$(cd "$2" && pwd -P); fi
      shift 2
      ;;
    *) usage ;;
  esac
done
root=$(cd "$(dirname "$0")/../.." && pwd)
host=$root/build/tools/leanexe-wasmtime-host
out=$root/build/verified
if [ -n "$reference" ]; then out=$root/build/byte-check/verified; fi
mkdir -p "$out"
if [ "$reference" = "$(cd "$out" && pwd -P)" ]; then
  echo "fail: byte reference and emission directories must differ" >&2
  exit 2
fi
cd "$root"
mode=checked
build=$root/.lake/build
lake_config=(-R)
if [ "$fast" -eq 1 ]; then
  mode=fast
  build=$root/.lake/build-fast
  lake_config=(-R -K fast=true)
  notice="fast: the kernel checks no proof of this package's modules, decide +kernel included,"
  notice+=" and the file theorems are not checked"
  echo "$notice"
fi
if command -v sha256sum > /dev/null 2>&1; then sum=(sha256sum); else sum=(shasum -a 256); fi
tmp=$(mktemp -d)
configured=0
ran=0
unchanged=0
unchecked=0
# Removes the temporary files, prints the counts of the checks, and, after a fast build, restores
# the checked configuration.
finish() {
  local status=$?
  rm -rf "$tmp"
  if [ -z "$reference" ]; then
    echo "checks: $ran ran, $unchanged unchanged since a recorded pass"
  fi
  if [ "$fast" -eq 1 ]; then
    echo "$notice"
    echo "fast: file theorem checks not run: $unchecked"
    if [ "$configured" -eq 1 ] && ! tools/leanrun --timeout 10m lake -R env true; then
      echo "fail: Lake's checked configuration was not restored; run lake -R" >&2
      status=1
    fi
  fi
  exit "$status"
}
trap finish EXIT
# The case executable of the module that --cases names: its entry in
# tests/verified/case-generators.txt, or verified-cases.
cases_exe=$(awk -F: -v name="$case_module" '$1 == name { print $2 }' \
  tests/verified/case-generators.txt)
cases_exe=${cases_exe:-verified-cases}
# Without --cases, the cases come from verified-cases and from the executables of the modules
# whose cases it does not import, which link Mathlib or take long to build.
case_exes=("$cases_exe")
if [ -z "$case_module" ]; then
  case_exes+=(verified-cases-arraytrees verified-cases-buffertrees verified-cases-sgp4box
    verified-cases-sgp4omm verified-cases-attitude verified-cases-qmethod verified-cases-screening
    verified-cases-chisquare verified-cases-gate verified-cases-assignment verified-cases-events
    verified-cases-avoidance verified-cases-passivesafety verified-cases-orbit verified-cases-frames
    verified-cases-geolocation)
fi
# The modules that `lean` and `lean --run` read for the files given are their imports, less the
# toolchain's own.
imports() {
  sed -n -E 's/^import ([A-Za-z0-9_.]+).*/\1/p' "$@" |
    { grep -v -E '^(Init|Std|Lean|Lake)(\.|$)' || true; }
}
# Whether the part of the check for module $1 runs: every part without --cases, and with it only
# the part of its module.
runs() {
  [ -z "$case_module" ] || [ "$case_module" = "$1" ]
}
targets=($(imports tools/Emit.lean))
while IFS=: read -r module constant name; do
  if runs "$name"; then
    targets+=("$module")
  fi
done <"$root/tests/verified/modules.txt"
if [ -z "$reference" ]; then
  if runs gpt; then targets+=($(imports tests/gpt/Cases.lean)); fi
  if runs euler || runs sums; then
    targets+=($(imports tests/TestSupport/Native/ModuleCases.lean))
  fi
  if runs slew; then targets+=(TestSupport.Slew.EdgesMain $(imports tests/slew/Axioms.lean)); fi
  if [ "$case_module" = "slew" ]; then
    targets+=(Demos.Slew.Verified $(imports Demos/Slew/File.lean))
  fi
  if runs energy; then targets+=($(imports tests/energy/Axioms.lean)); fi
  if runs conjunction; then targets+=($(imports tests/conjunction/Axioms.lean)); fi
  if [ "$case_module" = "conjunction" ]; then
    targets+=(Demos.Conjunction.Verified $(imports Demos/Conjunction/File.lean))
  fi
  if runs accuracy; then targets+=($(imports tests/conjunction/AccuracyAxioms.lean)); fi
  if [ "$case_module" = "accuracy" ]; then
    targets+=(Demos.Conjunction.AccuracyVerified $(imports Demos/Conjunction/AccuracyFile.lean))
  fi
  if runs adaptive; then targets+=($(imports tests/conjunction/AdaptiveAxioms.lean)); fi
  if [ "$case_module" = "adaptive" ]; then
    targets+=(Demos.Conjunction.AdaptiveVerified $(imports Demos/Conjunction/AdaptiveFile.lean))
  fi
  if runs attitude; then targets+=($(imports tests/attitude/Axioms.lean)); fi
  if [ "$case_module" = "attitude" ]; then
    targets+=(Demos.Attitude.Verified $(imports Demos/Attitude/File.lean))
  fi
  if runs qmethod; then targets+=($(imports tests/attitude/QAxioms.lean)); fi
  if [ "$case_module" = "qmethod" ]; then
    targets+=(Demos.Attitude.QVerified $(imports Demos/Attitude/QFile.lean))
  fi
  if runs screening; then targets+=($(imports tests/screening/Axioms.lean)); fi
  if [ "$case_module" = "screening" ]; then
    targets+=(Demos.Screening.Verified $(imports Demos/Screening/File.lean))
  fi
  if runs chisquare; then targets+=($(imports tests/gate/ChiSquareAxioms.lean)); fi
  if [ "$case_module" = "chisquare" ]; then
    targets+=(Demos.Gate.Verified $(imports Demos/Gate/File.lean))
  fi
  if runs gate; then targets+=($(imports tests/gate/GateAxioms.lean)); fi
  if [ "$case_module" = "gate" ]; then
    targets+=(Demos.Gate.GateVerified $(imports Demos/Gate/GateFile.lean))
  fi
  if runs assignment; then targets+=($(imports tests/gate/AssignmentAxioms.lean)); fi
  if [ "$case_module" = "assignment" ]; then
    targets+=(Demos.Gate.AssignmentVerified $(imports Demos/Gate/AssignmentFile.lean))
  fi
  if runs events; then targets+=($(imports tests/events/Axioms.lean)); fi
  if [ "$case_module" = "events" ]; then
    targets+=(Demos.Events.Verified $(imports Demos/Events/File.lean))
  fi
  if runs avoidance; then targets+=($(imports tests/avoidance/Axioms.lean)); fi
  if [ "$case_module" = "avoidance" ]; then
    targets+=(Demos.Avoidance.Verified $(imports Demos/Avoidance/File.lean))
  fi
  if runs sgp4; then targets+=($(imports tests/sgp4/Axioms.lean)); fi
  if runs passivesafety; then targets+=($(imports tests/passivesafety/Axioms.lean)); fi
  if [ "$case_module" = "passivesafety" ]; then
    targets+=(Demos.PassiveSafety.Verified $(imports Demos/PassiveSafety/File.lean))
  fi
  if [ "$case_module" = "sgp4" ]; then
    targets+=(Demos.Sgp4.Verified $(imports Demos/Sgp4/File.lean))
  fi
  if runs sgp4box; then targets+=($(imports tests/sgp4/BoxAxioms.lean)); fi
  if [ "$case_module" = "sgp4box" ]; then
    targets+=(Demos.Sgp4.BoxVerified $(imports Demos/Sgp4/BoxFile.lean))
  fi
  if runs sgp4omm; then targets+=($(imports tests/sgp4/OmmAxioms.lean)); fi
  if [ "$case_module" = "sgp4omm" ]; then
    targets+=(Demos.Sgp4.OmmVerified $(imports Demos/Sgp4/OmmFile.lean))
  fi
  if [ "$case_module" = "energy" ]; then
    targets+=(Demos.Energy.Verified $(imports Demos/Energy/File.lean))
  fi
  if runs gibbs || runs lambert; then targets+=($(imports tests/orbit/Axioms.lean)); fi
  if [ "$case_module" = "gibbs" ]; then
    targets+=(Demos.Orbit.GibbsVerified $(imports Demos/Orbit/GibbsFile.lean))
  fi
  if [ "$case_module" = "lambert" ]; then
    targets+=(Demos.Orbit.LambertVerified $(imports Demos/Orbit/LambertFile.lean))
  fi
  if [ "$case_module" = "frames" ]; then
    targets+=(Demos.Frames.Verified $(imports Demos/Frames/File.lean)
      $(imports tests/frames/Axioms.lean))
  fi
  if [ "$case_module" = "geolocation" ]; then
    targets+=(Demos.Geolocation.Verified $(imports Demos/Geolocation/File.lean)
      $(imports tests/geolocation/Axioms.lean))
  fi
  if [ -z "$case_module" ]; then
    while IFS=: read -r name theorem file; do
      targets+=("$theorem" $(imports "$file"))
    done <"$root/tests/verified/numerics.txt"
  fi
  if runs heapsums; then targets+=($(imports tests/verified/HeapSumsAxioms.lean)); fi
  if runs typedtrees; then
    targets+=($(imports tests/verified/TypedTreesAxioms.lean tests/verified/TreeFieldConditions.lean))
  fi
  if runs arraytrees; then targets+=($(imports tests/verified/ArrayTreesOrder.lean)); fi
  if runs buffertrees; then targets+=($(imports tests/verified/BufferTreesOrder.lean)); fi
  if [ "$case_module" != "gpt" ] && [ "$case_module" != "euler" ]; then targets+=("${case_exes[@]}"); fi
  if [ -z "$case_module" ]; then
    targets+=($(imports tests/TestSupport/Numerics/*Accuracy.lean \
      Library/Numerics/Arithmetic/Uscale/UscaleCheck.lean))
  fi
fi
configured=1
tools/leanrun --timeout 12h lake "${lake_config[@]}" --log-level error build "${targets[@]}"
# The hash of the file $1.
digest() {
  "${sum[@]}" <"$1" | cut -d' ' -f1
}
# The hash of standard input.
key() {
  "${sum[@]}" | cut -d' ' -f1
}
# The file of the record of check $1.
record_file() {
  echo "$records/$(tr ' /' '__' <<<"$1")"
}
# Whether the record of check $1 holds $2.  Without the cache no record counts.
recorded() {
  local file
  file=$(record_file "$1")
  [ "$cache" -eq 1 ] && [ -f "$file" ] && [ "$(cat "$file")" = "$2" ]
}
# Runs check $1 with the command that follows $2 unless its record holds $2, and records $2 after
# the command passes.  The command exits the script when it fails.
check() {
  local id=$1 inputs=$2
  shift 2
  if recorded "$id" "$inputs"; then
    echo "unchanged: $id"
    unchanged=$((unchanged + 1))
    return 0
  fi
  rm -f "$(record_file "$id")"
  echo "run: $id"
  "$@"
  echo "$inputs" >"$(record_file "$id")"
  ran=$((ran + 1))
}
# The names of this package's modules.
package='^(LeanExe|Library|Demos|Verified|Examples|TestSupport)([.]|$)'
if [ -z "$reference" ]; then
  records=$root/build/verified-checks/$mode
  mkdir -p "$records"
  # The build hash of each module of this package, from its .olean file.
  oleans=$tmp/oleans
  (cd "$build/lib/lean" && find . -name '*.olean' -print0 | xargs -0 "${sum[@]}") |
    awk '{ m = substr($2, 3); sub(/\.olean$/, "", m); gsub("/", ".", m); print m, $1 }' >"$oleans"
  # The imports of this package's modules among themselves, a line `MODULE IMPORT` for each.
  graph=$tmp/graph
  { find LeanExe Library Demos Verified Examples tests/TestSupport -name '*.lean'
    printf '%s\n' LeanExe.lean Library.lean Demos.lean Verified.lean Examples.lean
    echo tests/TestSupport.lean
  } | xargs awk -v package="$package" '
    FNR == 1 { m = FILENAME; sub(/^tests\//, "", m); sub(/\.lean$/, "", m); gsub("/", ".", m) }
    /^import / && $2 ~ package { print m, $2 }
  ' >"$graph"
  # The inputs that every check of Lean files shares: this script and the dependencies.
  common_inputs=$(
    "${sum[@]}" tests/verified/run.sh lean-toolchain lakefile.lean lake-manifest.json
    for dependency in .lake/packages/*/; do
      echo "$dependency $(git -C "$dependency" rev-parse HEAD)"
      git -C "$dependency" status --porcelain --untracked-files=no
    done
  )
  wasm_tools=$(wasm-tools --version)
fi
# The inputs of a check that reads Lean files and modules: the shared inputs, the hash of each
# file argument, and the build hash of every module of this package that is a module argument or
# that a file or module argument imports, directly or through other modules of this package.
lean_inputs() {
  local roots=() argument
  echo "$common_inputs"
  for argument in "$@"; do
    case "$argument" in
      *.lean) "${sum[@]}" "$argument"; roots+=($(imports "$argument")) ;;
      *) roots+=("$argument") ;;
    esac
  done
  awk -v roots="${roots[*]}" -v package="$package" '
    FILENAME == ARGV[1] { built[$1] = $2; next }
    { imported[$1] = imported[$1] " " $2 }
    END {
      n = split(roots, stack, " ")
      while (n > 0) {
        m = stack[n--]
        if ((m in seen) || m !~ package) continue
        seen[m] = 1
        k = split(imported[m], found, " ")
        for (i = 1; i <= k; i++) stack[++n] = found[i]
      }
      for (m in seen) print m, ((m in built) ? built[m] : "unbuilt")
    }' "$oleans" "$graph" | sort
}
emit() {
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$1" "$2" "$3"
  wasm-tools validate "$3"
}
emitted=0
while IFS=: read -r module constant name; do
  if [ -n "$case_module" ]; then
    [ "$name" = "$case_module" ] || continue
  fi
  emitted=$((emitted + 1))
  wasm=$out/$name.wasm
  if [ -n "$reference" ]; then
    emit "$module" "$constant" "$wasm"
    cmp "$reference/$name.wasm" "$wasm"
    echo "$name: bytes unchanged"
    continue
  fi
  # The record of an emission holds the hash of its inputs and the hash of the file it wrote.
  inputs=$({ lean_inputs tools/Emit.lean "$module"; echo "$wasm_tools $module $constant"; } | key)
  if [ -f "$wasm" ] && recorded "emit $name" "$inputs $(digest "$wasm")"; then
    echo "unchanged: emit $name"
    unchanged=$((unchanged + 1))
    continue
  fi
  rm -f "$(record_file "emit $name")"
  echo "run: emit $name"
  emit "$module" "$constant" "$wasm"
  echo "$inputs $(digest "$wasm")" >"$(record_file "emit $name")"
  ran=$((ran + 1))
done <"$root/tests/verified/modules.txt"
if [ "$emitted" -eq 0 ]; then
  echo "fail: unknown module $case_module" >&2
  exit 2
fi
if [ -n "$reference" ]; then
  echo "verified byte comparison passed: $emitted modules"
  exit 0
fi
if [ ! -x "$host" ] || [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  echo "fail: $host is missing or older than tools/wasmtime-host.c; build it with tools/build-wasmtime-host.sh" >&2
  exit 1
fi
# The host and, where ldd resolves it, the Wasmtime library that it loads.
host_inputs=$(
  "${sum[@]}" "$host"
  if command -v ldd > /dev/null 2>&1; then
    for library in $(ldd "$host" | awk '$1 ~ /^libwasmtime\./ && $3 ~ /^\// { print $3 }'); do
      "${sum[@]}" "$library"
    done
  fi
)
# The inputs of a check that runs the host on the written module $1, other than its Lean files.
host_check_inputs() {
  echo "$host_inputs"
  echo "$1.wasm $(digest "$out/$1.wasm")"
}
gpt() {
  tests/gpt/run.sh "$out/gpt.wasm"
  tests/gpt/sessions.sh "$out/gpt.wasm"
}
if [ -z "$case_module" ] || [ "$case_module" = "gpt" ]; then
  inputs=$({ host_check_inputs gpt; "${sum[@]}" tests/gpt/run.sh tests/gpt/sessions.sh
    lean_inputs tests/gpt/Cases.lean; } | key)
  check gpt "$inputs" gpt
  if [ "$case_module" = "gpt" ]; then
    exit 0
  fi
fi
# Checks the cases of tests/TestSupport/Native/ModuleCases.lean named $1 on the written module $2.
module_cases() {
  local inputs
  inputs=$({ host_check_inputs "$2"; "${sum[@]}" tests/modules/run.sh
    lean_inputs tests/TestSupport/Native/ModuleCases.lean; } | key)
  check "module cases $1" "$inputs" tests/modules/run.sh --module "$1" "$out/$2.wasm"
}
if [ -z "$case_module" ] || [ "$case_module" = "euler" ]; then
  module_cases euler euler
  if [ "$case_module" = "euler" ]; then
    exit 0
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "sums" ]; then
  module_cases shapes sums
fi
# Checks the file theorem module of a written module, unless the build is fast, and records the
# pass.
check_file() {
  local inputs
  if [ "$fast" -eq 1 ]; then
    echo "not checked in fast mode: file $1"
    unchecked=$((unchecked + 1))
    return 0
  fi
  inputs=$({ lean_inputs "$3"; echo "$1.wasm $(digest "$out/$1.wasm")"; } | key)
  check "file $1" "$inputs" file_theorems "$@"
}
# Checks the file theorem module of a written module: elaborates the file module against the file,
# after the build above has built the theorem module, and requires both of its axiom reports to
# name only the three permitted axioms.  The file module's second theorem depends on every byte
# theorem of the module, so its axiom report covers them all.
file_theorems() {
  local name=$1 theorem=$2 file=$3 reports axiom_counts
  reports=$(tools/leanrun --timeout 10m lake env lean "$file") || {
    echo "$reports"
    echo "fail: $file does not check against $out/$name.wasm" >&2
    exit 1
  }
  axiom_counts=$(awk '
    /depends on axioms: \[/ {
      report = $0
      while (report !~ /\]/ && (getline) > 0) report = report " " $0
      sub(/^.*depends on axioms: /, "", report)
      gsub(/[[:space:]]+/, " ", report)
      count++
      if (report == "[propext, Classical.choice, Quot.sound]") permitted++
    }
    END { print count + 0, permitted + 0 }' <<<"$reports")
  if [ "$axiom_counts" != "2 2" ]; then
    echo "$reports"
    echo "fail: the theorems of $file must report only the three permitted axioms" >&2
    exit 1
  fi
  echo "$name: $name.wasm holds the module of $theorem, with the permitted axioms"
}
# Checks the axiom audit $1 with the function $2, axiom_reports unless given, and records the pass.
check_axioms() {
  local inputs
  inputs=$(lean_inputs "$1" | key)
  check "audit $1" "$inputs" "${2:-axiom_reports}" "$1"
}
# Elaborates a file.
elaborates() {
  tools/leanrun --timeout 10m lake env lean "$1"
}
# Elaborates an axiom audit and requires every report in it to name only axioms among the three
# permitted ones.
axiom_reports() {
  local file=$1 reports verdict
  reports=$(tools/leanrun --timeout 10m lake env lean "$file") || {
    echo "$reports"
    echo "fail: $file does not elaborate" >&2
    exit 1
  }
  echo "$reports"
  verdict=$(awk '
    /depends on axioms: \[/ {
      report = $0
      while (report !~ /\]/ && (getline) > 0) report = report " " $0
      sub(/^.*depends on axioms: \[/, "", report)
      sub(/\].*$/, "", report)
      count++
      n = split(report, names, /,[[:space:]]*/)
      for (i = 1; i <= n; i++) {
        gsub(/[[:space:]]/, "", names[i])
        if (names[i] != "propext" && names[i] != "Classical.choice" && names[i] != "Quot.sound")
          bad++
      }
    }
    /does not depend on any axioms/ { count++ }
    END { print (count > 0 && bad == 0) ? "ok" : "fail" }' <<<"$reports")
  if [ "$verdict" != "ok" ]; then
    echo "fail: $file reports an axiom beyond propext, Classical.choice, and Quot.sound" >&2
    exit 1
  fi
}
if [ -z "$case_module" ] || [ "$case_module" = "slew" ]; then
  inputs=$({ host_check_inputs slew; "${sum[@]}" tests/slew/edges.sh
    lean_inputs tests/TestSupport/Slew/EdgesMain.lean; } | key)
  check "slew edges" "$inputs" tests/slew/edges.sh "$out/slew.wasm"
  check_axioms tests/slew/Axioms.lean elaborates
  if [ "$case_module" = "slew" ]; then
    check_file slew Demos.Slew.Verified Demos/Slew/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "energy" ]; then
  check_axioms tests/energy/Axioms.lean
  if [ "$case_module" = "energy" ]; then
    check_file energy Demos.Energy.Verified Demos/Energy/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "conjunction" ]; then
  check_axioms tests/conjunction/Axioms.lean
  if [ "$case_module" = "conjunction" ]; then
    check_file conjunction Demos.Conjunction.Verified Demos/Conjunction/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "accuracy" ]; then
  check_axioms tests/conjunction/AccuracyAxioms.lean
  if [ "$case_module" = "accuracy" ]; then
    check_file accuracy Demos.Conjunction.AccuracyVerified Demos/Conjunction/AccuracyFile.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "adaptive" ]; then
  check_axioms tests/conjunction/AdaptiveAxioms.lean
  if [ "$case_module" = "adaptive" ]; then
    check_file adaptive Demos.Conjunction.AdaptiveVerified Demos/Conjunction/AdaptiveFile.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "attitude" ]; then
  check_axioms tests/attitude/Axioms.lean
  if [ "$case_module" = "attitude" ]; then
    check_file attitude Demos.Attitude.Verified Demos/Attitude/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "qmethod" ]; then
  check_axioms tests/attitude/QAxioms.lean
  if [ "$case_module" = "qmethod" ]; then
    check_file qmethod Demos.Attitude.QVerified Demos/Attitude/QFile.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "screening" ]; then
  check_axioms tests/screening/Axioms.lean
  if [ "$case_module" = "screening" ]; then
    check_file screening Demos.Screening.Verified Demos/Screening/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "chisquare" ]; then
  check_axioms tests/gate/ChiSquareAxioms.lean
  if [ "$case_module" = "chisquare" ]; then
    check_file chisquare Demos.Gate.Verified Demos/Gate/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "gate" ]; then
  check_axioms tests/gate/GateAxioms.lean
  if [ "$case_module" = "gate" ]; then
    check_file gate Demos.Gate.GateVerified Demos/Gate/GateFile.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "assignment" ]; then
  check_axioms tests/gate/AssignmentAxioms.lean
  if [ "$case_module" = "assignment" ]; then
    check_file assignment Demos.Gate.AssignmentVerified Demos/Gate/AssignmentFile.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "events" ]; then
  check_axioms tests/events/Axioms.lean
  if [ "$case_module" = "events" ]; then
    check_file events Demos.Events.Verified Demos/Events/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "avoidance" ]; then
  check_axioms tests/avoidance/Axioms.lean
  if [ "$case_module" = "avoidance" ]; then
    check_file avoidance Demos.Avoidance.Verified Demos/Avoidance/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "sgp4" ]; then
  check_axioms tests/sgp4/Axioms.lean
  if [ "$case_module" = "sgp4" ]; then
    check_file sgp4 Demos.Sgp4.Verified Demos/Sgp4/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "passivesafety" ]; then
  check_axioms tests/passivesafety/Axioms.lean
  if [ "$case_module" = "passivesafety" ]; then
    check_file passivesafety Demos.PassiveSafety.Verified Demos/PassiveSafety/File.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "sgp4box" ]; then
  check_axioms tests/sgp4/BoxAxioms.lean
  if [ "$case_module" = "sgp4box" ]; then
    check_file sgp4box Demos.Sgp4.BoxVerified Demos/Sgp4/BoxFile.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "sgp4omm" ]; then
  check_axioms tests/sgp4/OmmAxioms.lean
  if [ "$case_module" = "sgp4omm" ]; then
    check_file sgp4omm Demos.Sgp4.OmmVerified Demos/Sgp4/OmmFile.lean
  fi
fi
if [ -z "$case_module" ] || [ "$case_module" = "gibbs" ] || [ "$case_module" = "lambert" ]; then
  check_axioms tests/orbit/Axioms.lean
  if [ "$case_module" = "gibbs" ]; then
    check_file gibbs Demos.Orbit.GibbsVerified Demos/Orbit/GibbsFile.lean
  fi
  if [ "$case_module" = "lambert" ]; then
    check_file lambert Demos.Orbit.LambertVerified Demos/Orbit/LambertFile.lean
  fi
fi
if [ "$case_module" = "frames" ]; then
  check_axioms tests/frames/Axioms.lean
  check_file frames Demos.Frames.Verified Demos/Frames/File.lean
fi
if [ "$case_module" = "geolocation" ]; then
  check_axioms tests/geolocation/Axioms.lean
  check_file geolocation Demos.Geolocation.Verified Demos/Geolocation/File.lean
fi
# Each entry names the written module, the theorem module, and the file theorem module.
if [ -z "$case_module" ]; then
while IFS=: read -r name theorem file; do
  check_file "$name" "$theorem" "$file"
done <"$root/tests/verified/numerics.txt"
fi
if [ -z "$case_module" ] || [ "$case_module" = "heapsums" ]; then
  check_axioms tests/verified/HeapSumsAxioms.lean elaborates
fi
if [ -z "$case_module" ] || [ "$case_module" = "typedtrees" ]; then
  check_axioms tests/verified/TypedTreesAxioms.lean elaborates
  check_axioms tests/verified/TreeFieldConditions.lean elaborates
fi
if [ -z "$case_module" ] || [ "$case_module" = "arraytrees" ]; then
  check_axioms tests/verified/ArrayTreesOrder.lean elaborates
fi
if [ -z "$case_module" ] || [ "$case_module" = "buffertrees" ]; then
  check_axioms tests/verified/BufferTreesOrder.lean elaborates
fi
cases=$tmp/cases
errors=$tmp/errors
# Native Lean panics on the reads and updates past the end of an array that the cases exercise: it
# writes a message and a backtrace to standard error.  A read returns Lean's default element,
# an update the array unchanged, and insertIdx! an empty array.  The run fails when Lean exits
# with an error or writes any other message.
: >"$cases"
: >"$errors"
for exe in "${case_exes[@]}"; do
  if ! tools/leanrun --timeout 10m "$build/bin/$exe" >>"$cases" 2>>"$errors"; then
    cat "$errors" >&2
    echo "fail: native Lean exited with an error in $exe" >&2
    exit 1
  fi
done
counts=$(awk '
  $0 == "Error: index out of bounds" { reads++; next }
  /^PANIC at Array\.insertIdx! Init\.Data\.Array\.Basic:[0-9]+:[0-9]+: invalid index$/ { inserts++; next }
  $0 == "backtrace:" || /\[0x[0-9a-f]+\]$/ { next }
  { others++; print > "/dev/stderr" }
  END { print reads + 0, inserts + 0, others + 0 }' "$errors")
read -r reads inserts others <<<"$counts"
if [ "$others" -ne 0 ]; then
  echo "fail: native Lean wrote $others unexpected lines to standard error, shown above" >&2
  exit 1
fi
awk -F'|' '
  BEGIN { OFS = FS }
  NR == FNR { targets[$1 FS $2] = $3 FS $4; next }
  { print; key = $1 FS $2 }
  key in targets {
    split(targets[key], target, FS)
    $1 = target[1]; $2 = target[2]; print
  }' "$root/tests/verified/library-cases.txt" "$cases" >"$cases.library"
mv "$cases.library" "$cases"
echo "native Lean: $reads accesses past the end and $inserts insertIdx! past the end, as the cases expect"
passed=0
failed=0
skipped=0
lines=$tmp/lines
# The cases of each module run unless its record holds the hash of its case lines, its written
# module, the host, and this script, which a pass of all of them records.
for name in $(awk -F'|' '!seen[$1]++ { print $1 }' "$cases"); do
  if [ -n "$case_module" ] && [ "$name" != "$case_module" ]; then
    continue
  fi
  awk -F'|' -v name="$name" '$1 == name' "$cases" >"$lines"
  inputs=$({ host_check_inputs "$name"; "${sum[@]}" tests/verified/run.sh
    echo "cases $(digest "$lines")"; } | key)
  if recorded "cases $name" "$inputs"; then
    echo "unchanged: cases $name"
    unchanged=$((unchanged + 1))
    skipped=$((skipped + $(wc -l <"$lines")))
    continue
  fi
  rm -f "$(record_file "cases $name")"
  echo "run: cases $name"
  before=$failed
  while IFS='|' read -r _ export result args expected live allocsMax; do
    read -ra argv <<<"$args"
    if [ "$expected" = "trap" ]; then
      if "$host" call "$out/$name.wasm" "$export" "$result" "${argv[@]}" >/dev/null 2>"$errors"; then
        failed=$((failed + 1))
        echo "fail: $name $export $args: returned, expected a trap at unreachable"
      elif grep -q 'wasm `unreachable` instruction executed' "$errors"; then
        passed=$((passed + 1))
      else
        failed=$((failed + 1))
        echo "fail: $name $export $args: $(cat "$errors"), expected a trap at unreachable"
      fi
      continue
    fi
    if [ -z "$live" ]; then
      got=$("$host" call "$out/$name.wasm" "$export" "$result" "${argv[@]}" | paste -sd' ')
      held=""
    else
      output=$("$host" call-stats "$out/$name.wasm" "$export" "$result" "${argv[@]}")
      got=$(sed '$d' <<<"$output" | paste -sd' ')
      read -r _ allocs frees < <(tail -n 1 <<<"$output")
      held=$((allocs - frees))
    fi
    if [ -n "$allocsMax" ] && [ "$allocs" -gt "$allocsMax" ]; then
      failed=$((failed + 1))
      echo "fail: $name $export $args: $allocs allocations, at most $allocsMax expected"
    elif [ "$got" = "$expected" ] && [ "$held" = "$live" ]; then
      passed=$((passed + 1))
    else
      failed=$((failed + 1))
      echo "fail: $name $export $args: $got, expected $expected; live blocks $held, expected $live"
    fi
  done <"$lines"
  if [ "$failed" -eq "$before" ]; then
    echo "$inputs" >"$(record_file "cases $name")"
  fi
  ran=$((ran + 1))
done
echo "verified: passed $passed failed $failed"
if [ "$skipped" -ne 0 ]; then
  echo "verified: $skipped cases of unchanged modules not run"
fi
[ $((passed + skipped)) -gt 0 ] && [ "$failed" -eq 0 ] || exit 1
# Without --cases, every module of the registry has a case, except the modules of
# tests/verified/no-cases.txt, which other drivers test.
if [ -z "$case_module" ]; then
  missing=$(cut -d'|' -f1 "$cases" | sort -u |
    comm -13 - <(cut -d: -f3 "$root/tests/verified/modules.txt" | sort -u) |
    comm -23 - <(cut -d' ' -f1 "$root/tests/verified/no-cases.txt" | sort -u))
  if [ -n "$missing" ]; then
    echo "fail: modules without cases: $(paste -sd' ' <<<"$missing")" >&2
    exit 1
  fi
fi
if [ -n "$case_module" ]; then
  exit 0
fi
# Runs the native check $2 with the time limit $1, with the data files that follow as further
# inputs, and records the pass.
accuracy() {
  local limit=$1 file=$2 inputs
  shift 2
  inputs=$({ lean_inputs "$file"; [ "$#" -eq 0 ] || "${sum[@]}" "$@"; } | key)
  check "accuracy $file" "$inputs" tools/leanrun --timeout "$limit" lake env lean --run "$file"
}
# The accuracy of Trig.sin and Trig.cos against a reference computed with Lean's integers, in
# native Lean.
accuracy 10m tests/TestSupport/Numerics/TrigAccuracy.lean
# The behavior of the Fourier transforms, in native Lean.
accuracy 10m tests/TestSupport/Numerics/FourierAccuracy.lean
# The accuracy of exp, expm1, tanh, log, log1p, atan, atan2, asin, acos, tan, sinh, cosh, asinh,
# acosh, atanh, exp2, exp10, log2, log10, pow, sinpi, cospi, tanpi, erf, and erfc against
# references computed with Lean's integers, in native Lean.
accuracy 10m tests/TestSupport/Numerics/ExpAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/TanhAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/LogAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/Log1pAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/AtanAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/AsinAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/TanAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/SinhAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/AsinhAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/Exp2Accuracy.lean
accuracy 10m tests/TestSupport/Numerics/Log2Accuracy.lean
accuracy 10m tests/TestSupport/Numerics/PowAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/SinpiAccuracy.lean
accuracy 10m tests/TestSupport/Numerics/ErfAccuracy.lean
# The accuracy of tgamma, lgamma, the Bessel functions, and CORE-MATH's erfc against references
# computed with Lean's integers, in native Lean.
accuracy 30m tests/TestSupport/Numerics/TgammaAccuracy.lean
accuracy 30m tests/TestSupport/Numerics/LgammaAccuracy.lean
accuracy 30m tests/TestSupport/Numerics/BesselAccuracy.lean
accuracy 30m tests/TestSupport/Numerics/ErfcAccuracy.lean
# The software fused multiply-add against the exact value rounded to the nearest double, in native
# Lean.
accuracy 10m tests/TestSupport/Numerics/FmaAccuracy.lean
# The limb arithmetic of the string conversions against Lean's natural numbers, in native Lean.
accuracy 10m Library/Numerics/Arithmetic/Uscale/UscaleCheck.lean
# The decimal parsers and printers against references computed with Lean's integers, in native Lean.
accuracy 10m tests/TestSupport/Numerics/ParseFloatAccuracy.lean data/strconv/parse-cases.txt
accuracy 10m tests/TestSupport/Numerics/PrintFloatAccuracy.lean data/strconv/print-cases.txt
