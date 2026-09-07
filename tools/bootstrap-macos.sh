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

install_archive https://github.com/leanprover/lean4/releases/download/v4.34.0-rc2 \
  lean-4.34.0-rc2-darwin_aarch64.tar.zst \
  ca79a92a15c56d0270d9cdba936a07933efd14a7de635b55b09801979ce73909 \
  lean-4.34.0-rc2-darwin_aarch64
install_archive https://nodejs.org/dist/v24.13.0 \
  node-v24.13.0-darwin-arm64.tar.xz \
  c59a517e9147f25c6167426875a571432f1478c1d7ee7ecc10baa46b0d0e8545 \
  node-v24.13.0-darwin-arm64
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
