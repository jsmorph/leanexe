#!/usr/bin/env sh
# Builds build/tools/leanexe-cuda-host from tools/cuda-host.c against the CUDA driver API.
# CUDA_HOME names the toolkit whose cuda.h the host uses (default /usr/local/cuda); the driver's
# libcuda comes from the system.
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
CUDA=${CUDA_HOME:-/usr/local/cuda}
OUT=${LEANEXE_CUDA_HOST:-"$ROOT/build/tools/leanexe-cuda-host"}

if [ ! -f "$CUDA/include/cuda.h" ]; then
  printf '%s\n' "missing $CUDA/include/cuda.h; set CUDA_HOME" >&2
  exit 1
fi

mkdir -p "$(dirname -- "$OUT")"
cc -std=c11 -O2 -Wall -Wextra -Werror -I"$CUDA/include" "$ROOT/tools/cuda-host.c" -lcuda -o "$OUT"
printf '%s\n' "$OUT"
