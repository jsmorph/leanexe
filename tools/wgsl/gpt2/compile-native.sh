#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
cd "$root"
if [ "$(uname -s)" = Darwin ]; then . tools/macos-env.sh; fi
out="$root/build/gpt2/bundle"
c_api=${WASMTIME_C_API:-"$root/build/tools/wasmtime/wasmtime-v44.0.0-x86_64-linux-c-api"}
wgpu=${LEANEXE_WGPU_SOURCE:-"$root/build/tools/wgpu-native-768f15f6-vulkan"}
crypto="-lcrypto"
if [ "$(uname -s)" = Darwin ]; then crypto=""; fi
cc -std=c11 -O2 -Wall -Wextra -Werror -I"$c_api/include" -I"$wgpu/ffi" -I"$wgpu/ffi/webgpu-headers" -I"$out" \
  tools/wgsl/gpt2/native.c -L"$c_api/lib" -lwasmtime -Wl,-rpath,"$c_api/lib" \
  -L"$wgpu/target/release" -lwgpu_native -Wl,-rpath,"$wgpu/target/release" $crypto -o "$out/gpt2"
