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
node tools/wgsl/gpt2/body-shaders.js "$generation"
for index in 0 1 2 3 4 5; do
  cp "$generation/$index/kernel.wgsl" "$out/kernel-$index.wgsl"
done
python3 tools/wgsl/gpt2/manifest.py "$out"
tools/wgsl/gpt2/compile-native.sh
for name in index.html app.js host.js; do
  if [ -f "tools/wgsl/gpt2/$name" ]; then cp "tools/wgsl/gpt2/$name" "$out/$name"; fi
done
python3 tools/wgsl/gpt2/archive.py "$out"
printf 'Built %s\n' "$out"
