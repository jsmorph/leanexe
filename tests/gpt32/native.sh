#!/usr/bin/env bash
# Runs tests/gpt32/VerifiedNative.lean on SwiftShader and llvmpipe and on the verified gpt32.wasm in
# the Wasm host of the browser page: small random models through the Lean driver of
# Demos/Gpt32/Generate.lean, with the verified compiler's kernels and every step's scores compared
# bit for bit with native Lean's step32.
# Usage: tests/gpt32/native.sh [build directory]
set -euo pipefail
export PATH="$PATH:$HOME/.cargo/bin"
root=$(cd "$(dirname "$0")/../.." && pwd)
build=${1:-$root/build}
host=$root/build/tools/leanexe-webgpu-host
source=tests/gpt32/VerifiedNative.lean
(cd "$root" && tools/leanrun --timeout 20m lake --log-level error build Demos.Gpt32.NativeCases)
mkdir -p "$build/gpt32-native"
wasm=$build/gpt32-native/gpt32.wasm
(cd "$root" && tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Demos.Gpt32.Verified Demos.Gpt32.Verified.compiled.module "$wasm")
wasm-tools validate "$wasm"
echo "wasm:"
(cd "$root" && LEANEXE_GPT32_WASM="$wasm" tools/leanrun --timeout 30m lake env lean --run \
  "$source" "$root/tools/gpt32-wasm-host.mjs" "$build/gpt32-wasm")
for driver in /usr/lib/chromium/vk_swiftshader_icd.json /usr/share/vulkan/icd.d/lvp_icd.json; do
  echo "$(basename "$driver" .json):"
  (cd "$root" && VK_ICD_FILENAMES=$driver tools/leanrun --timeout 30m lake env lean --run \
    "$source" "$host" "$build/gpt32-native")
done
