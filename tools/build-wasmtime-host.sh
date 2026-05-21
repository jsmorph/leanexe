#!/usr/bin/env sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
WASMTIME_C_API=${WASMTIME_C_API:-"$ROOT/build/tools/wasmtime/wasmtime-v44.0.0-aarch64-linux-c-api"}
OUT=${LEANEXE_WASMTIME_HOST:-"$ROOT/build/tools/leanexe-wasmtime-host"}

if [ ! -f "$WASMTIME_C_API/include/wasmtime.h" ] || [ ! -f "$WASMTIME_C_API/lib/libwasmtime.so" ]; then
  printf '%s\n' "missing Wasmtime C API at $WASMTIME_C_API" >&2
  printf '%s\n' "download wasmtime-v44.0.0-aarch64-linux-c-api.tar.xz into build/tools/wasmtime" >&2
  exit 1
fi

mkdir -p "$(dirname -- "$OUT")"
cc \
  -std=c11 \
  -Wall \
  -Wextra \
  -Werror \
  -I"$WASMTIME_C_API/include" \
  "$ROOT/tools/wasmtime-host.c" \
  -L"$WASMTIME_C_API/lib" \
  -lwasmtime \
  -Wl,-rpath,'$ORIGIN/wasmtime/wasmtime-v44.0.0-aarch64-linux-c-api/lib' \
  -o "$OUT"

printf '%s\n' "$OUT"
