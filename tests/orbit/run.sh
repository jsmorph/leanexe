#!/usr/bin/env bash
# The reference test of the orbit-determination programs.  It builds the case executable and
# runs tests/orbit/reference.py, which checks Demos.Orbit.gibbsBounds and
# Demos.Orbit.lambertBounds in native Lean against 50-digit oracles, a two-body propagator, and a
# transcription of Izzo's binary64 code.  It writes the report to build/orbit/reference.txt.
# Usage: tests/orbit/run.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$root/build/orbit
mkdir -p "$out"
tools/leanrun --timeout 60m lake --log-level error build verified-cases-orbit
uv run tests/orbit/reference.py .lake/build/bin/verified-cases-orbit | tee "$out/reference.txt"
