#!/bin/sh
set -eu
set -f

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

tools/leanrun --timeout 15m --log build/running-sum/arithmetic-build.log lake build \
  Demos.RunningSum.Compiled
tools/leanrun --timeout 5m lake env lean tests/running-sum/Axioms.lean
tools/leanrun --timeout 5m lake env lean --run tests/running-sum/Arithmetic.lean
