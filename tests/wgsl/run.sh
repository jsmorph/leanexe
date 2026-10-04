#!/usr/bin/env bash
# Runs every case of tests/wgsl/Cases.lean on SwiftShader and llvmpipe with the kernel text that
# Project/WGSL/Emit.lean prints, and compares the output words with native Lean's.  The kernels
# and the cases stay in the build directory's wgsl/, where tests/wgsl/serve.py serves them to the
# browser page of tests/wgsl/browser.
# Usage: tests/wgsl/run.sh [build directory]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
build=${1:-$root/build}
host=$root/build/tools/leanexe-webgpu-host
mkdir -p "$build/wgsl"
for entry in Project.WGSL.Binary32:Project.WGSL:scale Project.WGSL.Binary32:Project.WGSL:axpyArray \
    Project.WGSL.Binary32:Project.WGSL:matVec Project.WGSL.Binary32:Project.WGSL:condMix \
    Project.Gpt32.Kernels:Project.Gpt32:exp Project.Gpt32.Specs:Project.Gpt32:embed \
    Project.Gpt32.Specs:Project.Gpt32:layerNorm Project.Gpt32.Specs:Project.Gpt32:linear \
    Project.Gpt32.Specs:Project.Gpt32:append Project.Gpt32.Specs:Project.Gpt32:scores \
    Project.Gpt32.Specs:Project.Gpt32:headMax Project.Gpt32.Specs:Project.Gpt32:headSum \
    Project.Gpt32.Specs:Project.Gpt32:probs Project.Gpt32.Specs:Project.Gpt32:mix \
    Project.Gpt32.Specs:Project.Gpt32:add Project.Gpt32.Specs:Project.Gpt32:gelu \
    Project.Gpt32.Specs:Project.Gpt32:logits; do
  IFS=: read -r module namespace kernel <<<"$entry"
  (cd "$root" && tools/leanrun --timeout 10m lake env lean --run Project/WGSL/Emit.lean \
    "$module" "$namespace.${kernel}Kernel" "$build/wgsl/$kernel.wgsl")
done
cases=$build/wgsl/cases.txt
# Reads past the end of a shorter array with `!` print panic messages from native Lean, which then
# returns the default 0; they are expected.
(cd "$root" && tools/leanrun --timeout 10m lake env lean --run tests/wgsl/Cases.lean) >"$cases" \
  2>/dev/null
status=0
for driver in /usr/lib/chromium/vk_swiftshader_icd.json /usr/share/vulkan/icd.d/lvp_icd.json; do
  passed=0
  failed=0
  while IFS='|' read -r kernel groups output inputs expected; do
    read -ra argv <<<"$inputs"
    out=$(VK_ICD_FILENAMES=$driver "$host" run "$build/wgsl/$kernel.wgsl" main "$groups" \
      "$output" "${argv[@]}")
    if [ "$out" = "$expected" ]; then
      passed=$((passed + 1))
    else
      failed=$((failed + 1))
      echo "fail: $kernel on $(basename "$driver") with $groups workgroups: $out, expected $expected"
    fi
  done <"$cases"
  echo "$(basename "$driver" .json): passed $passed failed $failed"
  [ "$failed" -eq 0 ] || status=1
done
exit $status
