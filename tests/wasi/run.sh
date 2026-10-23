#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

tools/leanrun --timeout 10m --log build/wasi/foundations.log lake build \
  Verified.Bytes.CopyOwned Verified.Bytes.Release Verified.Bytes.Get LeanExe.Wasi.Prefix
tools/leanrun --timeout 5m lake env lean tests/wasi/Bytes.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/Code.lean
tools/leanrun --timeout 5m lake env lean tests/wasi/Axioms.lean
