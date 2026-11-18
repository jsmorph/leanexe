#!/bin/sh
# Checks the pure core of the unbiased random choice of Demos/RandomChoice.  It checks the hashes of
# the reviewed specification and samples against spec.sha256, builds the demo's modules, and
# elaborates tests/random-choice/Axioms.lean, which restates the call theorems of the pure core and
# the counting theorems and fails on an axiom other than propext, Classical.choice, and
# Quot.sound.  The pure module's samples run in `tests/verified/run.sh --cases randomChoice`.
# Usage: tests/random-choice/run.sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
out="$root/build/random-choice"
mkdir -p "$out"
if ! sha256sum --quiet -c Demos/RandomChoice/spec.sha256; then
  printf 'random choice spec: Spec.lean or Samples.lean differs from the reviewed version\n' >&2
  exit 1
fi
tools/leanrun --timeout 60m --log "$out/build.log" lake build Demos.RandomChoice.Compiled \
  Demos.RandomChoice.Unbiased Demos.RandomChoice.CommandProof
tools/leanrun --timeout 10m lake env lean tests/random-choice/Axioms.lean
