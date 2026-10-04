#!/usr/bin/env sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
VERSION=${WGPU_NATIVE_VERSION:-29.0.1.1}
BASE_URL=${WGPU_NATIVE_BASE_URL:-"https://github.com/gfx-rs/wgpu-native/releases/download/v$VERSION"}

detect_platform() {
  system=$(uname -s)
  machine=$(uname -m)
  case "$system:$machine" in
    Linux:aarch64 | Linux:arm64)
      printf '%s\n' "linux-aarch64"
      ;;
    Linux:x86_64 | Linux:amd64)
      printf '%s\n' "linux-x86_64"
      ;;
    *)
      printf '%s\n' "unsupported wgpu-native platform: $system $machine" >&2
      exit 1
      ;;
  esac
}

PLATFORM=${WGPU_NATIVE_PLATFORM:-$(detect_platform)}
DEST="$ROOT/build/tools/wgpu-native"
NAME="wgpu-$PLATFORM-release"
ARCHIVE="$DEST/$NAME.zip"

# The SHA-256 digests GitHub publishes for the release assets.
case "$VERSION:$PLATFORM" in
  29.0.1.1:linux-aarch64)
    DEFAULT_SHA256=015fcdf1dbae82e614a783cc38017e5399ae0927a889fe9b69c9b664bc61b47a
    ;;
  29.0.1.1:linux-x86_64)
    DEFAULT_SHA256=95a4d90c071005a98d03eab348beaa6b07e16eb00d1dcdb9f8348f75eb97ec5a
    ;;
  *)
    DEFAULT_SHA256=
    ;;
esac

SHA256=${WGPU_NATIVE_SHA256:-$DEFAULT_SHA256}

if [ -z "$SHA256" ]; then
  printf '%s\n' "no checked wgpu-native archive hash for version $VERSION on $PLATFORM" >&2
  printf '%s\n' "set WGPU_NATIVE_SHA256 for this override" >&2
  exit 2
fi

for tool in sha256sum unzip; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf '%s\n' "$tool is required to install wgpu-native" >&2
    exit 127
  fi
done

archive_sha256() {
  if ! output=$(sha256sum "$1"); then
    printf '%s\n' "failed to calculate SHA-256: $1" >&2
    return 1
  fi
  printf '%s\n' "${output%% *}"
}

mkdir -p "$DEST"
if [ -f "$ARCHIVE" ] && [ "$(archive_sha256 "$ARCHIVE")" != "$SHA256" ]; then
  printf '%s\n' "cached wgpu-native archive has the wrong SHA-256: $ARCHIVE" >&2
  printf '%s\n' "downloading a replacement" >&2
  rm -f "$ARCHIVE"
fi
if [ ! -f "$ARCHIVE" ]; then
  tmp="$ARCHIVE.part"
  rm -f "$tmp"
  if ! curl --fail --location --silent --show-error "$BASE_URL/$NAME.zip" --output "$tmp"; then
    rm -f "$tmp"
    exit 1
  fi
  actual=$(archive_sha256 "$tmp")
  if [ "$actual" != "$SHA256" ]; then
    printf '%s\n' "downloaded wgpu-native archive has the wrong SHA-256" >&2
    printf '%s\n' "expected $SHA256, got $actual" >&2
    rm -f "$tmp"
    exit 1
  fi
  mv -f "$tmp" "$ARCHIVE"
fi

DIR="$DEST/v$VERSION-$PLATFORM"
if [ ! -d "$DIR" ]; then
  unzip -q "$ARCHIVE" -d "$DIR.part"
  mv "$DIR.part" "$DIR"
fi

printf 'WGPU_NATIVE=%s\n' "$DIR"
