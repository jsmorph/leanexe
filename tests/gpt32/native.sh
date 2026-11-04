#!/usr/bin/env bash
# Runs tests/gpt32/VerifiedNative.lean on each device of LIST: small random models through the Lean
# driver of Demos/Gpt32/Generate.lean, with the verified compiler's kernels and every step's scores
# compared bit for bit with native Lean's step32.  The devices are `wasm`, the verified gpt32.wasm
# in the Wasm host of the browser page; `swiftshader` and `llvmpipe`, the WGSL kernels on those
# Vulkan drivers through leanexe-webgpu-host; and `cuda`, the PTX kernels on the GPU through
# leanexe-cuda-host, after which the script records the SHA-256 of each cubin.
# Usage: tests/gpt32/native.sh [--devices LIST] [build directory]
# LIST is comma-separated, by default wasm,swiftshader,llvmpipe.
set -euo pipefail
devices=wasm,swiftshader,llvmpipe
if [ "${1:-}" = --devices ]; then
  devices=$2
  shift 2
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
build=${1:-$root/build}
source=tests/gpt32/VerifiedNative.lean
(cd "$root" && tools/leanrun --timeout 20m lake --log-level error build Demos.Gpt32.NativeCases)
IFS=, read -r -a list <<<"$devices"
for device in "${list[@]}"; do
  echo "$device:"
  case $device in
    wasm)
      if ! command -v wasm-tools > /dev/null 2>&1; then
        echo "gpt32 native: wasm-tools is not on the search path" >&2
        exit 1
      fi
      mkdir -p "$build/gpt32-native"
      wasm=$build/gpt32-native/gpt32.wasm
      (cd "$root" && tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
        Demos.Gpt32.Verified Demos.Gpt32.Verified.compiled.module "$wasm")
      wasm-tools validate "$wasm"
      (cd "$root" && LEANEXE_GPT32_WASM="$wasm" tools/leanrun --timeout 30m lake env lean --run \
        "$source" wgsl "$root/tools/gpt32-wasm-host.mjs" "$build/gpt32-wasm")
      ;;
    swiftshader | llvmpipe)
      if [ "$device" = swiftshader ]; then
        icd=/usr/lib/chromium/vk_swiftshader_icd.json
      else
        icd=/usr/share/vulkan/icd.d/lvp_icd.json
      fi
      (cd "$root" && VK_ICD_FILENAMES=$icd tools/leanrun --timeout 30m lake env lean --run \
        "$source" wgsl "$root/build/tools/leanexe-webgpu-host" "$build/gpt32-native")
      ;;
    cuda)
      (cd "$root" && tools/leanrun --timeout 30m lake env lean --run \
        "$source" ptx "$root/build/tools/leanexe-cuda-host" "$build/gpt32-cuda")
      (cd "$build/gpt32-cuda/kernels" && sha256sum ./*.cubin) >"$build/gpt32-cuda/cubins.sha256"
      ;;
    *)
      echo "gpt32 native: unknown device $device" >&2
      exit 2
      ;;
  esac
done
