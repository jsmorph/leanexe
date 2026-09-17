#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
cd "$root"
if [ "$(uname -s)" = Darwin ]; then . tools/macos-env.sh; fi
out="$root/build/gpt128-demo"
mkdir -p "$out"
tools/leanrun --timeout 90s --lock-timeout 10 lake build lean-wasm > "$out/compiler-build.log" 2>&1
tools/leanrun --timeout 90s --lock-timeout 10 lake -d proofs/talos/lean build Project.TinyGpt2Seq.Model > "$out/model-build.log" 2>&1
tools/leanrun --timeout 90s --lock-timeout 10 lake -d proofs/talos/lean env "$root/.lake/build/bin/lean-wasm" compile --module Project.TinyGpt2Seq.Model --entry Project.TinyGpt2Seq.hidden --out "$out/hidden.wasm"
python3 tools/wgsl/demo/transfer.py "$out/transfer.wat"
"${WASM_TOOLS:-wasm-tools}" parse "$out/transfer.wat" -o "$out/transfer.wasm"
"${WASM_TOOLS:-wasm-tools}" validate "$out/hidden.wasm"
"${WASM_TOOLS:-wasm-tools}" validate "$out/transfer.wasm"
python3 tools/wgsl/demo/pack.py "$root" "$out"
if [ -f tools/wgsl/demo/host.js ] && [ -f tools/wgsl/demo/app.js ]; then
  cp tools/wgsl/demo/index.html tools/wgsl/demo/app.js tools/wgsl/demo/host.js "$out/"
fi
c_api=${WASMTIME_C_API:-"$root/build/tools/wasmtime/wasmtime-v44.0.0-x86_64-linux-c-api"}
wgpu=${LEANEXE_WGPU_SOURCE:-"$root/build/tools/wgpu-native-768f15f6-vulkan"}
crypto="-lcrypto"
if [ "$(uname -s)" = Darwin ]; then crypto=""; fi
cc -std=c11 -O2 -Wall -Wextra -Werror -I"$c_api/include" -I"$wgpu/ffi" -I"$wgpu/ffi/webgpu-headers" -I"$out" \
  tools/wgsl/demo/native.c -L"$c_api/lib" -lwasmtime -Wl,-rpath,"$c_api/lib" \
  -L"$wgpu/target/release" -lwgpu_native -Wl,-rpath,"$wgpu/target/release" $crypto -o "$out/gpt128"
printf 'Built %s\n' "$out"
