#!/bin/sh
set -eu
set -f

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

tools/leanrun --timeout 10m --log build/wasi/script-host-build.log lake build \
  Verified.Wasi.ScriptHostContracts Verified.Examples.WasiCodegen
tools/leanrun --timeout 5m lake env lean tests/wasi/ScriptHostAxioms.lean
tools/leanrun --timeout 5m lake env lean --run tests/wasi/ScriptHost.lean
