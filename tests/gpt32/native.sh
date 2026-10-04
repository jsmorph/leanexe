#!/usr/bin/env bash
# Runs tests/gpt32/Native.lean on SwiftShader and llvmpipe: small random models through the Lean
# driver of Project/Gpt32/Generate.lean, with every step's scores compared bit for bit with
# native Lean's step32.
# Usage: tests/gpt32/native.sh [build directory]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
build=${1:-$root/build}
host=$root/build/tools/leanexe-webgpu-host
for driver in /usr/lib/chromium/vk_swiftshader_icd.json /usr/share/vulkan/icd.d/lvp_icd.json; do
  echo "$(basename "$driver" .json):"
  (cd "$root" && VK_ICD_FILENAMES=$driver tools/leanrun --timeout 30m lake env lean --run \
    tests/gpt32/Native.lean "$host" "$build/gpt32-native")
done
