#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
cd "$root"
if [ "$(uname -s)" = Darwin ]; then . tools/macos-env.sh; fi
c_api=${WASMTIME_C_API:?Set WASMTIME_C_API}
wgpu=${LEANEXE_WGPU_SOURCE:-"$root/build/tools/wgpu-native-768f15f6-vulkan"}
out="$root/build/tools/leanexe-packed-wgsl-host"
cc -std=c11 -O2 -Wall -Wextra -Werror -DLEANEXE_WGSL_PACKED_HOST \
  -I"$c_api/include" -I"$wgpu/ffi" -I"$wgpu/ffi/webgpu-headers" \
  tools/wasmtime-host.c -L"$c_api/lib" -lwasmtime -Wl,-rpath,"$c_api/lib" \
  -L"$wgpu/target/release" -lwgpu_native -Wl,-rpath,"$wgpu/target/release" -o "$out"
printf '%s\n' "$out"
