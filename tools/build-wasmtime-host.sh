#!/usr/bin/env sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
VERSION=${WASMTIME_VERSION:-44.0.0}
OUT=${LEANEXE_WASMTIME_HOST:-"$ROOT/build/tools/leanexe-wasmtime-host"}

detect_platform() {
  system=$(uname -s)
  machine=$(uname -m)
  case "$system:$machine" in
    Linux:aarch64 | Linux:arm64)
      printf '%s\n' "aarch64-linux"
      ;;
    Linux:x86_64 | Linux:amd64)
      printf '%s\n' "x86_64-linux"
      ;;
    *)
      printf '%s\n' "unsupported Wasmtime platform: $system $machine" >&2
      exit 1
      ;;
  esac
}

PLATFORM=${WASMTIME_PLATFORM:-$(detect_platform)}
DEFAULT_C_API="$ROOT/build/tools/wasmtime/wasmtime-v$VERSION-$PLATFORM-c-api"
if [ "${WASMTIME_C_API+x}" ]; then
  C_API="$WASMTIME_C_API"
  RPATH="$C_API/lib"
else
  C_API="$DEFAULT_C_API"
  RPATH="\$ORIGIN/wasmtime/wasmtime-v$VERSION-$PLATFORM-c-api/lib"
fi

if [ ! -f "$C_API/include/wasmtime.h" ] || [ ! -f "$C_API/lib/libwasmtime.so" ]; then
  printf '%s\n' "missing Wasmtime C API at $C_API" >&2
  printf '%s\n' "run tools/download-wasmtime.sh or set WASMTIME_C_API" >&2
  exit 1
fi

mkdir -p "$(dirname -- "$OUT")"
cc \
  -std=c11 \
  -Wall \
  -Wextra \
  -Werror \
  -I"$C_API/include" \
  "$ROOT/tools/wasmtime-host.c" \
  -L"$C_API/lib" \
  -lwasmtime \
  -Wl,-rpath,"$RPATH" \
  -o "$OUT"

printf '%s\n' "$OUT"
