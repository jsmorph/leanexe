#!/usr/bin/env sh
# Builds tests/ptx/nearest.c against the CUDA driver API and runs it: cvt.rni.f32.f32 with the
# replacement of a NaN by 0x7fc00000, compared with C's nearbyintf on all 2^32 binary32 inputs.
# CUDA_HOME names the toolkit whose cuda.h the program uses (default /usr/local/cuda).
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
CUDA=${CUDA_HOME:-/usr/local/cuda}
OUT=$ROOT/build/tools/ptx-nearest

if [ ! -f "$CUDA/include/cuda.h" ]; then
  printf '%s\n' "missing $CUDA/include/cuda.h; set CUDA_HOME" >&2
  exit 1
fi
mkdir -p "$(dirname -- "$OUT")"
cc -std=c11 -O2 -Wall -Wextra -Werror -I"$CUDA/include" "$ROOT/tests/ptx/nearest.c" -lcuda -lm \
  -o "$OUT"
"$OUT"
