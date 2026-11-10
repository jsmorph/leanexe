#!/usr/bin/env bash
# The Python mirror of the delimited framing, tests/baremetal/delim_frame.py, against the Lean
# definitions of LeanExe/Requests/Delimited.lean and the echo of records of
# tests/TestSupport/M7/Delim.lean.  It builds TestSupport.M7.Delim, writes N cases of each kind
# from the seed SEED with delim_frame.py gen, 2,000 cases and the seed 20261109 unless given:
# records for cobsEncode, encodings with random corruptions for cobsDecode, and streams of
# encoded records with corruptions, empty segments, and overlong segments for delimAnswers of
# echoMach.  tests/baremetal/DelimMirror.lean answers each case with the Lean definitions under
# lake env lean --run, and delim_frame.py check requires every answer to equal the mirror's and
# the mirror's encodings of the two records of section 5.8 of the BMS design to equal the
# design's wire bytes.  UV names uv.  The products lie in OUT, build/baremetal/delim-mirror unless
# set.
# Usage: tests/baremetal/delim-mirror.sh [SEED [N]]
set -euo pipefail
[ "$#" -le 2 ] || { echo "usage: tests/baremetal/delim-mirror.sh [SEED [N]]" >&2; exit 2; }
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/delim-mirror}")
uv=${UV:-uv}
mkdir -p "$out"
rm -f "${out:?}"/cases "${out:?}"/lean
tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build \
  TestSupport.M7.Delim
"$uv" run tests/baremetal/delim_frame.py gen "${1:-20261109}" "${2:-2000}" "$out/cases"
tools/leanrun --timeout 30m --memory-high "${MEM:-8G}" lake env lean --run \
  tests/baremetal/DelimMirror.lean "$out/cases" "$out/lean"
"$uv" run tests/baremetal/delim_frame.py check "$out/cases" "$out/lean"
