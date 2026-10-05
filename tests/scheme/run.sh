#!/usr/bin/env bash
# Compile the arena/VM through leanexe, emit actual WASM, compare it with native Lean.
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p build/scheme
node tests/scheme/corpus.mjs
node tests/scheme/compiler.mjs
tools/leanrun --timeout 15m lake --log-level=error build \
  Project.Scheme.Tests Project.Scheme.Module Project.Pipeline.Emit scheme-native
tools/leanrun --timeout 60s lake env lean --run Project/Scheme/RunTests.lean
tools/leanrun --timeout 60s lake env .lake/build/bin/scheme-native build/scheme/native.json
tools/leanrun --timeout 120s lake env lean --run Project/Pipeline/Emit.lean \
  Project.Scheme.Module Project.Scheme.scheme.module build/scheme/scheme.wasm
node tests/scheme/wasm.mjs build/scheme/scheme.wasm build/scheme/native.json
