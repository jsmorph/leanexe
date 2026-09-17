#!/bin/sh
# Execute WGSL through the existing harness and native SwiftShader CPU driver.
set -eu
repo=$(CDPATH= cd "$(dirname "$0")/../.." && pwd)
python=${LEANEXE_WGPU_PYTHON:-"$repo/build/wgsl/macos-venv-20260916/bin/python"}
WGPU_LIB_PATH=${LEANEXE_WGPU_NATIVE_LIB:-"$repo/build/tools/wgpu-native-768f15f6-vulkan/target/release/libwgpu_native.dylib"}
driver=${LEANEXE_SWIFTSHADER_DIR:-"/Applications/Google Chrome.app/Contents/Frameworks/Google Chrome Framework.framework/Versions/152.0.7977.84/Libraries"}
for required in "$python" "$WGPU_LIB_PATH" "$driver/libvulkan.dylib" "$driver/libvk_swiftshader.dylib" "$driver/vk_swiftshader_icd.json"; do
  if [ ! -f "$required" ]; then
    printf 'Missing CPU runtime file: %s\nSee tools/wgsl/README.md for setup.\n' "$required" >&2
    exit 1
  fi
done
DYLD_LIBRARY_PATH="$driver${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
VK_ICD_FILENAMES="$driver/vk_swiftshader_icd.json"
VK_DRIVER_FILES="$VK_ICD_FILENAMES"
WGPU_BACKEND_TYPE=Vulkan
export WGPU_LIB_PATH DYLD_LIBRARY_PATH VK_ICD_FILENAMES VK_DRIVER_FILES WGPU_BACKEND_TYPE
exec "$python" "$repo/tools/wgsl/run.py" "$@" --backend Vulkan --adapter SwiftShader
