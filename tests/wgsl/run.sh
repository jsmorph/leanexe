#!/usr/bin/env bash
# Runs WGSL kernels on SwiftShader and llvmpipe with the kernel text that tools/EmitWgsl.lean
# prints, on cases whose expected output words native Lean computes, and compares the words.
# By default the kernels are the verified compiler's: those of Examples/Binary32/Compiled.lean under
# the names scale, axpyArray, matVec, and condMix, and those of Demos/Gpt32/Verified.lean under the
# names that the GPT-2 host commands use, with the cases of tests/wgsl/Cases.lean and of
# Demos/Gpt32/VerifiedGpuCasesMain.lean.  The kernels and the cases stay in the build directory's
# wgsl/, where tests/web/serve.py serves them to the browser pages.
# With `--verified`, the kernels are those of Verified/Examples/Wgsl.lean and those of
# Examples/Binary32/Compiled.lean under their own names, with the cases of
# Verified/Examples/WgslCasesMain.lean, in the same directory.
# `--emit-only` writes the kernels and the cases and stops, and `--drivers-only` runs existing ones
# on the drivers, so that the drivers can run on a host without Lean.
# Usage: tests/wgsl/run.sh [--verified] [--emit-only|--drivers-only] [build directory]
set -euo pipefail
set_name=default
stage=all
while [ "$#" -gt 0 ]; do
  case "$1" in
    --verified) set_name=verified ;;
    --emit-only) stage=emit ;;
    --drivers-only) stage=drivers ;;
    *) break ;;
  esac
  shift
done
root=$(cd "$(dirname "$0")/../.." && pwd)
build=${1:-$root/build}
host=$root/build/tools/leanexe-webgpu-host
gpt32_kernels="exp embed layerNorm linear append scores headMax headSum probs mix add gelu logits"
# Each kernel as MODULE:CONSTANT:NAME, where NAME.wgsl receives the text of CONSTANT.
kernels=()
case "$set_name" in
  default)
    out=$build/wgsl
    modules=(Examples.Binary32.Compiled Demos.Gpt32.Verified Demos.Gpt32.VerifiedGpuCasesMain)
    case_sources=(tests/wgsl/Cases.lean Demos/Gpt32/VerifiedGpuCasesMain.lean)
    for k in Scale:scale AxpyArray:axpyArray MatVec:matVec CondMix:condMix; do
      kernels+=("Examples.Binary32.Compiled:Examples.Binary32.verified${k%%:*}32Kernel:${k#*:}")
    done
    for k in $gpt32_kernels; do
      kernels+=("Demos.Gpt32.Verified:Demos.Gpt32.Verified.${k}Kernel:$k")
    done
    ;;
  verified)
    out=$build/wgsl
    modules=(Verified.Examples.WgslCasesMain Examples.Binary32.Compiled)
    case_sources=(Verified/Examples/WgslCasesMain.lean)
    for k in verifiedScale verifiedBranch verifiedFlags verifiedWords verifiedRoots; do
      kernels+=("Verified.Examples.Wgsl:Verified.Examples.Wgsl.${k}Kernel:$k")
    done
    for k in verifiedScale32 verifiedAxpyArray32 verifiedMatVec32 verifiedCondMix32; do
      kernels+=("Examples.Binary32.Compiled:Examples.Binary32.${k}Kernel:$k")
    done
    ;;
esac
mkdir -p "$out"
cases=$out/cases.txt
if [ "$stage" != drivers ]; then
  (cd "$root" && tools/leanrun --timeout 20m lake --log-level error build LeanExe.WGSL.Parse \
    "${modules[@]}")
  for entry in "${kernels[@]}"; do
    IFS=: read -r module constant kernel <<<"$entry"
    (cd "$root" && tools/leanrun --timeout 10m lake env lean --run tools/EmitWgsl.lean \
      "$module" "$constant" "$out/$kernel.wgsl")
  done
  # Reads past the end of a shorter array with `!` print panic messages from native Lean, which then
  # returns the default 0; they are expected.
  : >"$cases"
  for source in "${case_sources[@]}"; do
    log=$out/$(basename "$source" .lean).stderr.log
    if (cd "$root" && tools/leanrun --timeout 10m lake env lean --run "$source") >>"$cases" \
        2>"$log"; then
      true
    else
      result=$?
      cat "$log" >&2
      exit "$result"
    fi
  done
fi
if [ "$stage" = emit ]; then
  exit 0
fi
status=0
for driver in /usr/lib/chromium/vk_swiftshader_icd.json /usr/share/vulkan/icd.d/lvp_icd.json; do
  passed=0
  failed=0
  case_number=0
  failures=$out/$(basename "$driver" .json).failures.txt
  : >"$failures"
  while IFS='|' read -r kernel groups output inputs expected; do
    case_number=$((case_number + 1))
    read -ra argv <<<"$inputs"
    printf '%s|%s|%s|%s|%s|%s\n' "$case_number" "$kernel" "$groups" "$output" "$inputs" \
      "$expected" >"$out/current-case.txt"
    if result_words=$(VK_ICD_FILENAMES=$driver "$host" run "$out/$kernel.wgsl" main "$groups" \
        "$output" "${argv[@]}" 2>"$out/host.stderr.log"); then
      true
    else
      result=$?
      cat "$out/host.stderr.log" >&2
      echo "host failed: $kernel on $(basename "$driver") case $case_number, status $result; input in $out/current-case.txt" >&2
      exit "$result"
    fi
    if [ "$result_words" = "$expected" ]; then
      passed=$((passed + 1))
    else
      failed=$((failed + 1))
      printf '%s|%s|%s|%s|%s|%s\n' "$case_number" "$kernel" "$groups" "$output" "$inputs" \
        "$expected" >>"$failures"
      printf 'actual|%s\n' "$result_words" >>"$failures"
      echo "fail: $kernel on $(basename "$driver") case $case_number; values in $failures"
    fi
  done <"$cases"
  echo "$(basename "$driver" .json): passed $passed failed $failed"
  [ "$failed" -eq 0 ] || status=1
done
exit $status
