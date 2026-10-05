#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p build/smalltalk
node tests/smalltalk/corpus.mjs
node tests/smalltalk/compiler.mjs
tools/leanrun --timeout 15m lake --log-level=error build \
  Project.Smalltalk.Control Project.Smalltalk.Module Project.Pipeline.Emit smalltalk-native
tools/leanrun --timeout 120s lake env .lake/build/bin/smalltalk-native
tools/leanrun --timeout 120s lake env lean --run Project/Pipeline/Emit.lean \
  Project.Smalltalk.Module Project.Smalltalk.smalltalk.module build/smalltalk/smalltalk.wasm
node tests/smalltalk/wasm.mjs
