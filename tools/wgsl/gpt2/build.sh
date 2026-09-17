#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)
cd "$root"
if [ "$(uname -s)" = Darwin ]; then . tools/macos-env.sh; fi
work="$root/build/gpt2"
out="$work/bundle"
python=${GPT2_BUILD_PYTHON:-"$work/venv/bin/python"}
mkdir -p "$out"
if [ ! -x "$python" ]; then
  "${GPT2_PYTHON:-python3.13}" -m venv "$work/venv"
  "$python" -m pip install -r tools/wgsl/gpt2/requirements-build.txt
fi
python3 tools/wgsl/gpt2/download.py "$work/source"
"$python" tools/wgsl/gpt2/pack.py "$work/source" "$out"
tools/leanrun --timeout 90s --lock-timeout 10 lake build lean-wasm > "$work/compiler-build.log" 2>&1
tools/leanrun --timeout 90s --lock-timeout 10 lake -d proofs/talos/lean build Project.Gpt2.Model Project.Gpt2.Tokenizer > "$work/model-build.log" 2>&1
tools/leanrun --timeout 90s --lock-timeout 10 lake -d proofs/talos/lean env "$root/.lake/build/bin/lean-wasm" compile --module Project.Gpt2.Model --entry Project.Gpt2.compute --out "$out/model.wasm"
tools/leanrun --timeout 90s --lock-timeout 10 lake -d proofs/talos/lean env "$root/.lake/build/bin/lean-wasm" compile --module Project.Gpt2.Tokenizer --entry Project.Gpt2.Tokenizer.tokens --out "$out/tokenizer.wasm"
python3 tools/wgsl/gpt2/transfer.py "$work/transfer.wat"
"${WASM_TOOLS:-wasm-tools}" parse "$work/transfer.wat" -o "$out/transfer.wasm"
for name in model tokenizer transfer; do "${WASM_TOOLS:-wasm-tools}" validate "$out/$name.wasm"; done
generation=$(mktemp -d "$work/generation-XXXXXX")
index=0
for shape in 2304:768 768:768 3072:768 768:3072 25129:768 25128:768; do
  columns=${shape%:*}; inner=${shape#*:}
  tools/leanrun --timeout 90s --lock-timeout 10 lake env lean --run tools/wgsl/Generate.lean "$generation/$index" 1 "$columns" "$inner" separate
  cp "$generation/$index/kernel.wgsl" "$out/kernel-$index.wgsl"
  index=$((index+1))
done
python3 tools/wgsl/gpt2/manifest.py "$out"
c_api=${WASMTIME_C_API:-"$root/build/tools/wasmtime/wasmtime-v44.0.0-x86_64-linux-c-api"}
wgpu=${LEANEXE_WGPU_SOURCE:-"$root/build/tools/wgpu-native-768f15f6-vulkan"}
crypto="-lcrypto"
if [ "$(uname -s)" = Darwin ]; then crypto=""; fi
cc -std=c11 -O2 -Wall -Wextra -Werror -I"$c_api/include" -I"$wgpu/ffi" -I"$wgpu/ffi/webgpu-headers" -I"$out" \
  tools/wgsl/gpt2/native.c -L"$c_api/lib" -lwasmtime -Wl,-rpath,"$c_api/lib" \
  -L"$wgpu/target/release" -lwgpu_native -Wl,-rpath,"$wgpu/target/release" $crypto -o "$out/gpt2"
for name in index.html app.js host.js; do
  if [ -f "tools/wgsl/gpt2/$name" ]; then cp "tools/wgsl/gpt2/$name" "$out/$name"; fi
done
printf 'Built %s\n' "$out"
