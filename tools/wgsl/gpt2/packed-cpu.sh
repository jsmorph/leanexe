#!/bin/sh
# Experimental packed-module host protocol, using native CPU WebGPU.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
: "${LEANEXE_PACKED_SHADERS:?Set LEANEXE_PACKED_SHADERS to a checked packed-shaders directory}"
if [ "$(uname -s)" = Darwin ]; then
  driver=${LEANEXE_SWIFTSHADER_DIR:-"/Applications/Google Chrome.app/Contents/Frameworks/Google Chrome Framework.framework/Versions/152.0.7977.84/Libraries"}
  [ -f "$driver/vk_swiftshader_icd.json" ] || { echo 'CPU Vulkan driver unavailable' >&2; exit 1; }
  DYLD_LIBRARY_PATH="$driver${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
  VK_ICD_FILENAMES="$driver/vk_swiftshader_icd.json"
  VK_DRIVER_FILES="$VK_ICD_FILENAMES"
  export DYLD_LIBRARY_PATH VK_ICD_FILENAMES VK_DRIVER_FILES
fi
exec "$root/build/tools/leanexe-packed-wgsl-host" "$@"
