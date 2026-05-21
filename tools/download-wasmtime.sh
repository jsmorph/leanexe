#!/usr/bin/env sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
VERSION=${WASMTIME_VERSION:-44.0.0}
BASE_URL=${WASMTIME_BASE_URL:-"https://github.com/bytecodealliance/wasmtime/releases/download/v$VERSION"}

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
DEST="$ROOT/build/tools/wasmtime"
CLI_NAME="wasmtime-v$VERSION-$PLATFORM"
C_API_NAME="wasmtime-v$VERSION-$PLATFORM-c-api"
CLI_ARCHIVE="$DEST/$CLI_NAME.tar.xz"
C_API_ARCHIVE="$DEST/$C_API_NAME.tar.xz"

download() {
  url=$1
  out=$2
  if [ -f "$out" ]; then
    return
  fi
  curl -L "$url" -o "$out"
}

extract() {
  archive=$1
  dir=$2
  if [ -d "$dir" ]; then
    return
  fi
  tar -C "$DEST" -xf "$archive"
}

mkdir -p "$DEST"
download "$BASE_URL/$CLI_NAME.tar.xz" "$CLI_ARCHIVE"
download "$BASE_URL/$C_API_NAME.tar.xz" "$C_API_ARCHIVE"
extract "$CLI_ARCHIVE" "$DEST/$CLI_NAME"
extract "$C_API_ARCHIVE" "$DEST/$C_API_NAME"

if [ -e "$DEST/current" ] && [ ! -L "$DEST/current" ]; then
  printf '%s\n' "$DEST/current exists and is not a symlink" >&2
  exit 1
fi

(
  cd "$DEST"
  ln -sfn "$CLI_NAME" current
)

printf 'WASMTIME=%s\n' "$DEST/current/wasmtime"
printf 'WASMTIME_C_API=%s\n' "$DEST/$C_API_NAME"
