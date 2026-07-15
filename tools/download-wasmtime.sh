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

case "$VERSION:$PLATFORM" in
  44.0.0:aarch64-linux)
    DEFAULT_CLI_SHA256=294cae921fb88cbbcb60a914eaaaf313df3249d718609afb5804186b3f1912f5
    DEFAULT_C_API_SHA256=6f1fb604f6d3f307f2d093bdc18e9781c85692e17c2360f5975875817adc34ab
    ;;
  44.0.0:x86_64-linux)
    DEFAULT_CLI_SHA256=52eba06fe9f4364aa6164a4a3eafb2ca692ba9a756cbe8137b5574871f8cbfc8
    DEFAULT_C_API_SHA256=e193aa35338637d84f172323a909cebb907c14c55b5a4b5bdbf89f5cd0b89c81
    ;;
  *)
    DEFAULT_CLI_SHA256=
    DEFAULT_C_API_SHA256=
    ;;
esac

CLI_SHA256=${WASMTIME_CLI_SHA256:-$DEFAULT_CLI_SHA256}
C_API_SHA256=${WASMTIME_C_API_SHA256:-$DEFAULT_C_API_SHA256}

if [ -z "$CLI_SHA256" ] || [ -z "$C_API_SHA256" ]; then
  printf '%s\n' "no checked Wasmtime archive hashes for version $VERSION on $PLATFORM" >&2
  printf '%s\n' "set WASMTIME_CLI_SHA256 and WASMTIME_C_API_SHA256 for this override" >&2
  exit 2
fi

if ! command -v sha256sum >/dev/null 2>&1; then
  printf '%s\n' "sha256sum is required to verify Wasmtime archives" >&2
  exit 127
fi

archive_sha256() {
  archive=$1
  if ! output=$(sha256sum "$archive"); then
    printf '%s\n' "failed to calculate SHA-256: $archive" >&2
    return 1
  fi
  printf '%s\n' "${output%% *}"
}

download() {
  url=$1
  out=$2
  expected=$3
  if [ -f "$out" ]; then
    actual=$(archive_sha256 "$out") || return 1
    if [ "$actual" = "$expected" ]; then
      return
    fi
    printf '%s\n' "cached Wasmtime archive has the wrong SHA-256: $out" >&2
    printf '%s\n' "expected $expected, got $actual" >&2
    printf '%s\n' "downloading a replacement" >&2
  fi

  tmp="$out.part"
  rm -f "$tmp"
  if ! curl --fail --location --silent --show-error "$url" --output "$tmp"; then
    rm -f "$tmp"
    return 1
  fi
  actual=$(archive_sha256 "$tmp") || {
    rm -f "$tmp"
    return 1
  }
  if [ "$actual" != "$expected" ]; then
    printf '%s\n' "downloaded Wasmtime archive has the wrong SHA-256: $url" >&2
    printf '%s\n' "expected $expected, got $actual" >&2
    rm -f "$tmp"
    return 1
  fi
  mv -f "$tmp" "$out"
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
download "$BASE_URL/$CLI_NAME.tar.xz" "$CLI_ARCHIVE" "$CLI_SHA256"
download "$BASE_URL/$C_API_NAME.tar.xz" "$C_API_ARCHIVE" "$C_API_SHA256"
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
