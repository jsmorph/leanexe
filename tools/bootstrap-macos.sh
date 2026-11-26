#!/bin/sh
# Install the project's existing pinned tools in fresh repository-local paths.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
[ "$(uname -sm)" = "Darwin arm64" ] || { echo "requires an ARM Mac" >&2; exit 2; }
dest="$root/build/tools"
mkdir -p "$dest"

install_archive() {
  url=$1
  archive=$2
  digest=$3
  directory=$4
  if [ ! -e "$dest/$archive" ]; then
    echo "Downloading $archive"
    curl --fail --location --silent --show-error --max-time 900 \
      "$url/$archive" --output "$dest/$archive"
  fi
  actual=$(shasum -a 256 "$dest/$archive")
  [ "${actual%% *}" = "$digest" ] || {
    echo "digest mismatch; preserving $dest/$archive for inspection" >&2
    exit 1
  }
  if [ -e "$dest/$directory" ]; then
    echo "Preserving existing $dest/$directory"
  else
    echo "Extracting verified $archive"
    tar -C "$dest" -xf "$dest/$archive"
  fi
}

install_archive https://github.com/leanprover/lean4/releases/download/v4.36.0 \
  lean-4.36.0-darwin_aarch64.tar.zst \
  49acada8749ad1343eff1224a3d2510ac61ed53363d37b5e738e8c587e7deabd \
  lean-4.36.0-darwin_aarch64
install_archive https://github.com/bytecodealliance/wasm-tools/releases/download/v1.251.0 \
  wasm-tools-1.251.0-aarch64-macos.tar.gz \
  ed0fdbdaa80a5c7ef434ac583e1d8df0b8e45d718b08edf28ec27a74e4029897 \
  wasm-tools-1.251.0-aarch64-macos
install_archive https://github.com/bytecodealliance/wasmtime/releases/download/v44.0.0 \
  wasmtime-v44.0.0-aarch64-macos.tar.xz \
  38a3b9d9fe64cee21bc9d9268e2c19fa35a7be59e030717545b84da0e6514eab \
  wasmtime-v44.0.0-aarch64-macos
install_archive https://github.com/bytecodealliance/wasmtime/releases/download/v44.0.0 \
  wasmtime-v44.0.0-aarch64-macos-c-api.tar.xz \
  d0877e9d23154aa5bd834475f76f8e2363580550ff9275c10d0c70de997675d2 \
  wasmtime-v44.0.0-aarch64-macos-c-api
echo "Pinned tools installed under $dest"
