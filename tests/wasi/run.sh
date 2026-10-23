#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

tools/leanrun --timeout 10m lake build LeanExe.Dialect.Bytes
tools/leanrun --timeout 5m lake env lean tests/wasi/Bytes.lean
