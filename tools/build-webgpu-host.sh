#!/usr/bin/env sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
VERSION=${WGPU_NATIVE_VERSION:-29.0.1.1}
OUT=${LEANEXE_WEBGPU_HOST:-"$ROOT/build/tools/leanexe-webgpu-host"}

case "$(uname -s):$(uname -m)" in
  Linux:aarch64 | Linux:arm64) PLATFORM=linux-aarch64 ;;
  Linux:x86_64 | Linux:amd64) PLATFORM=linux-x86_64 ;;
  *)
    printf '%s\n' "unsupported wgpu-native platform: $(uname -s) $(uname -m)" >&2
    exit 1
    ;;
esac

if [ "${WGPU_NATIVE+x}" ]; then
  LIB="$WGPU_NATIVE"
  RPATH="$LIB/lib"
else
  LIB="$ROOT/build/tools/wgpu-native/v$VERSION-$PLATFORM"
  RPATH="\$ORIGIN/wgpu-native/v$VERSION-$PLATFORM/lib"
fi

if [ ! -f "$LIB/include/webgpu/webgpu.h" ] || [ ! -f "$LIB/lib/libwgpu_native.so" ]; then
  printf '%s\n' "missing wgpu-native at $LIB" >&2
  printf '%s\n' "run tools/download-wgpu-native.sh or set WGPU_NATIVE" >&2
  exit 1
fi

mkdir -p "$(dirname -- "$OUT")"
cc \
  -std=c11 \
  -Wall \
  -Wextra \
  -Werror \
  -I"$LIB/include" \
  "$ROOT/tools/webgpu-host.c" \
  -L"$LIB/lib" \
  -lwgpu_native \
  -Wl,-rpath,"$RPATH" \
  -o "$OUT"

printf '%s\n' "$OUT"
