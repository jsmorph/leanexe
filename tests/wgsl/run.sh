#!/usr/bin/env bash
# Runs every case of tests/wgsl/Cases.lean on SwiftShader and llvmpipe with the kernel text that
# tools/EmitWgsl.lean prints, and compares the output words with native Lean's.  The kernels
# and the cases stay in the build directory's wgsl/, where tests/web/serve.py serves them to the
# browser page of tests/wgsl/browser.
# `--emit-only` writes the kernels and the cases and stops, and `--drivers-only` runs existing ones
# on the drivers, so that the drivers can run on a host without Lean.
# Usage: tests/wgsl/run.sh [--verified|--verified-gpt32] [--emit-only|--drivers-only] [build directory]
set -euo pipefail
verified=0
gpt32=0
stage=all
while [ "$#" -gt 0 ]; do
  case "$1" in
    --verified) verified=1 ;;
    --verified-gpt32) gpt32=1 ;;
    --emit-only) stage=emit ;;
    --drivers-only) stage=drivers ;;
    *) break ;;
  esac
  shift
done
root=$(cd "$(dirname "$0")/../.." && pwd)
build=${1:-$root/build}
host=$root/build/tools/leanexe-webgpu-host
mkdir -p "$build/wgsl"
cases=$build/wgsl/cases.txt
if [ "$stage" != drivers ]; then
  case_source=tests/wgsl/Cases.lean
  if [ "$verified" -eq 1 ]; then
    case_source=Verified/Examples/WgslCasesMain.lean
    (cd "$root" && tools/leanrun --timeout 10m lake --log-level error build Verified.Examples.WgslCasesMain)
  elif [ "$gpt32" -eq 1 ]; then
    (cd "$root" && tools/leanrun --timeout 20m lake --log-level error build \
      Demos.Gpt32.Verified Demos.Gpt32.VerifiedGpuCasesMain)
  fi
  for entry in Examples.Binary32.Wgsl:Examples.Binary32:scale Examples.Binary32.Wgsl:Examples.Binary32:axpyArray \
      Examples.Binary32.Wgsl:Examples.Binary32:matVec Examples.Binary32.Wgsl:Examples.Binary32:condMix \
      Demos.Gpt32.Kernels:Demos.Gpt32:exp Demos.Gpt32.Specs:Demos.Gpt32:embed \
      Demos.Gpt32.Specs:Demos.Gpt32:layerNorm Demos.Gpt32.Specs:Demos.Gpt32:linear \
      Demos.Gpt32.Specs:Demos.Gpt32:append Demos.Gpt32.Specs:Demos.Gpt32:scores \
      Demos.Gpt32.Specs:Demos.Gpt32:headMax Demos.Gpt32.Specs:Demos.Gpt32:headSum \
      Demos.Gpt32.Specs:Demos.Gpt32:probs Demos.Gpt32.Specs:Demos.Gpt32:mix \
      Demos.Gpt32.Specs:Demos.Gpt32:add Demos.Gpt32.Specs:Demos.Gpt32:gelu \
      Demos.Gpt32.Specs:Demos.Gpt32:logits \
      Verified.Examples.Wgsl:Verified.Examples.Wgsl:verifiedScale \
      Verified.Examples.Wgsl:Verified.Examples.Wgsl:verifiedBranch \
      Verified.Examples.Wgsl:Verified.Examples.Wgsl:verifiedFlags \
      Verified.Examples.Wgsl:Verified.Examples.Wgsl:verifiedWords \
      Verified.Examples.Wgsl:Verified.Examples.Wgsl:verifiedRoots; do
    IFS=: read -r module namespace kernel <<<"$entry"
    if [ "$gpt32" -eq 1 ]; then
      case "$module" in
        Demos.Gpt32.Kernels|Demos.Gpt32.Specs)
          module=Demos.Gpt32.Verified
          namespace=Demos.Gpt32.Verified
          ;;
        Examples.Binary32.Wgsl) true ;;
        *) continue ;;
      esac
    elif [ "$verified" -eq 1 ]; then
      [ "$module" = "Verified.Examples.Wgsl" ] || continue
    elif [ "$module" = "Verified.Examples.Wgsl" ]; then
      continue
    fi
    (cd "$root" && tools/leanrun --timeout 10m lake env lean --run tools/EmitWgsl.lean \
      "$module" "$namespace.${kernel}Kernel" "$build/wgsl/$kernel.wgsl")
  done
  # Reads past the end of a shorter array with `!` print panic messages from native Lean, which then
  # returns the default 0; they are expected.
  if (cd "$root" && tools/leanrun --timeout 10m lake env lean --run "$case_source") >"$cases" \
      2>"$build/wgsl/cases.stderr.log"; then
    true
  else
    result=$?
    cat "$build/wgsl/cases.stderr.log" >&2
    exit "$result"
  fi
  if [ "$gpt32" -eq 1 ]; then
    if (cd "$root" && tools/leanrun --timeout 10m lake env lean --run \
        Demos/Gpt32/VerifiedGpuCasesMain.lean) >>"$cases" \
        2>"$build/wgsl/gpt32-cases.stderr.log"; then
      true
    else
      result=$?
      cat "$build/wgsl/gpt32-cases.stderr.log" >&2
      exit "$result"
    fi
  fi
fi
if [ "$stage" = emit ]; then
  exit 0
fi
status=0
for driver in /usr/lib/chromium/vk_swiftshader_icd.json /usr/share/vulkan/icd.d/lvp_icd.json; do
  passed=0
  failed=0
  case_number=0
  failures=$build/wgsl/$(basename "$driver" .json).failures.txt
  : >"$failures"
  while IFS='|' read -r kernel groups output inputs expected; do
    case_number=$((case_number + 1))
    read -ra argv <<<"$inputs"
    printf '%s|%s|%s|%s|%s|%s\n' "$case_number" "$kernel" "$groups" "$output" "$inputs" \
      "$expected" >"$build/wgsl/current-case.txt"
    if out=$(VK_ICD_FILENAMES=$driver "$host" run "$build/wgsl/$kernel.wgsl" main "$groups" \
        "$output" "${argv[@]}" 2>"$build/wgsl/host.stderr.log"); then
      true
    else
      result=$?
      cat "$build/wgsl/host.stderr.log" >&2
      echo "host failed: $kernel on $(basename "$driver") case $case_number, status $result; input in $build/wgsl/current-case.txt" >&2
      exit "$result"
    fi
    if [ "$out" = "$expected" ]; then
      passed=$((passed + 1))
    else
      failed=$((failed + 1))
      printf '%s|%s|%s|%s|%s|%s\n' "$case_number" "$kernel" "$groups" "$output" "$inputs" \
        "$expected" >>"$failures"
      printf 'actual|%s\n' "$out" >>"$failures"
      echo "fail: $kernel on $(basename "$driver") case $case_number; values in $failures"
    fi
  done <"$cases"
  echo "$(basename "$driver" .json): passed $passed failed $failed"
  [ "$failed" -eq 0 ] || status=1
done
exit $status
