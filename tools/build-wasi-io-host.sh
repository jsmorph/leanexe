#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
case "$(uname -sm)" in
  'Linux x86_64') platform=x86_64-linux ;;
  'Linux aarch64') platform=aarch64-linux ;;
  'Darwin arm64') platform=aarch64-macos ;;
  *) echo "unsupported WASI I/O test host platform" >&2; exit 2 ;;
esac
api=${WASMTIME_C_API:-"$root/build/tools/wasmtime/wasmtime-v44.0.0-$platform-c-api"}
out=${LEANEXE_WASI_IO_HOST:-"$root/build/tools/leanexe-wasi-io-host"}
mkdir -p "$(dirname -- "$out")"
cc -std=c11 -O2 -Wall -Wextra -Werror -I"$api/include" \
  "$root/tools/wasi-io-host.c" -L"$api/lib" -lwasmtime \
  -Wl,-rpath,"$api/lib" -o "$out"
printf '%s\n' "$out"
