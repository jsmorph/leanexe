#!/bin/sh
set -eu
set -f
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

foundations_only=false
case "$#:${1-}" in
  0:) ;;
  1:--foundations-only) foundations_only=true ;;
  *) printf 'Usage: %s [--foundations-only]\n' "$0" >&2; exit 2 ;;
esac

tools/leanrun --timeout 10m --log build/wasi/foundations.log lake build \
  Verified.Bytes.CopyOwned Verified.Bytes.Release Verified.Bytes.Get \
  Verified.Bytes.Literal Verified.Bytes.StaticEnv Verified.BytesBuildCorrect \
  Verified.Wasi.Source Verified.Wasi.HostSpec Verified.Wasi.Scratch \
  Verified.Wasi.WrapperCode Verified.Wasi.Write Verified.Wasi.ReadCall \
  Verified.Wasi.ReadFrame Verified.Wasi.Runtime Verified.Wasi.RuntimeFrame \
  Verified.Wasi.ReadFunction Verified.Wasi.CallWrappers Verified.Wasi.WriteHelper \
  Verified.Wasi.ScratchContext Verified.Wasi.AfterScratch \
  Verified.Wasi.ReadCommand Verified.Wasi.WriteCommand \
  Verified.Wasi.Exit LeanExe.Wasi.Prefix \
  LeanExe.Wasi.Interpreter LeanExe.Wasi.RelatedExec LeanExe.Wasi.RelatedPrefix \
  Verified.Wasi.Program Verified.Wasi.ReflectLemmas Verified.Wasi.ReflectDefinitions \
  Verified.Wasi.ReturnCommand Verified.Wasi.CommandBind Verified.Wasi.CommandValue \
  Verified.Wasi.LoopControl Verified.Wasi.ReflectCases
tools/leanrun --timeout 10m --log build/wasi/transport.log lake build \
  Verified.Wasi.PureTransportSpecs Verified.Wasi.RelocationForms \
  Verified.Wasi.ModuleTransport Verified.Wasi.ModuleInitial Verified.Wasi.PurePrefix
tools/leanrun --timeout 5m lake env lean tests/wasi/TransportAxioms.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/WrapperAxioms.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/EffectAxioms.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/CommandAxioms.lean
tools/leanrun --timeout 5m lake env lean --run tests/wasi/Interpreter.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/Code.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/ExitModel.lean
if "$foundations_only"; then exit 0; fi
tools/leanrun --timeout 30m --log build/wasi/byte-values.log lake build \
  Verified.Examples.Bytes Verified.Examples.Literals
tools/leanrun --timeout 5m lake env lean tests/wasi/Bytes.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/Literals.lean
tools/leanrun --timeout 5m lake env lean tests/decoder/TableProfile.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/Axioms.lean

out="$root/build/wasi"
host="$root/build/tools/leanexe-wasmtime-host"
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.Bytes \
  Verified.Examples.Bytes.compiled.module "$out/bytes.wasm"
wasm-tools validate "$out/bytes.wasm"
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.Literals \
  Verified.Examples.Literals.compiled.module "$out/literals.wasm"
wasm-tools validate "$out/literals.wasm"

tab=$(printf '\t')
check_cases() {
  case_module=$1
  case_file=$2
  case_label=$3
  case_count=0
  while IFS="$tab" read -r export_name kind arguments expected allocations releases; do
    if [ "$expected" = _ ]; then expected=; fi
    if [ "$arguments" = _ ]; then set --; else set -- $arguments; fi
    observed=$("$host" call-stats "$case_module" "$export_name" "$kind" "$@")
    wanted=$(printf '%s\nstats %s %s' "$expected" "$allocations" "$releases")
    if [ "$observed" != "$wanted" ]; then
      printf '%s\n' "failed: $export_name $arguments" "expected: $wanted" "observed: $observed" >&2
      exit 1
    fi
    case_count=$((case_count + 1))
  done <"$case_file"
  printf '%s execution tests passed: %s cases\n' "$case_label" "$case_count"
}

check_cases "$out/bytes.wasm" "$root/tests/wasi/bytes.tsv" Byte
check_cases "$out/literals.wasm" "$root/tests/wasi/literals.tsv" Literal

count=0
while IFS="$tab" read -r export_name arguments; do
  set -- $arguments
  trap_log="$out/byte-trap-$count.log"
  if "$host" call "$out/bytes.wasm" "$export_name" bytes "$@" >"$trap_log" 2>&1; then
    printf 'Expected a trap: %s %s\n' "$export_name" "$arguments" >&2
    exit 1
  fi
  case "$(cat "$trap_log")" in
    *unreachable*) ;;
    *) cat "$trap_log" >&2; exit 1 ;;
  esac
  count=$((count + 1))
done <"$root/tests/wasi/byte-traps.tsv"
printf 'Byte trap tests passed: %s cases\n' "$count"
tests/wasi/codegen-run.sh
tests/wasi/reflection-run.sh
