#!/bin/sh
# Optional ARM Mac setup: isolated pinned Rust and Vulkan-enabled wgpu-native.
# SwiftShader and the Python environment are separate; see README.md.
set -eu
repo=$(CDPATH= cd "$(dirname "$0")/../.." && pwd)
cd "$repo"
git status --short --branch
test "$(uname -s)" = Darwin
test "$(uname -m)" = arm64
prefix="$repo/build/tools/rust-wgsl-1.90.0"
archives="$repo/build/tools/rust-wgsl-archives"
source_dir="$repo/build/tools/wgpu-native-768f15f6-vulkan"
revision=768f15f6ace8e4ec8e8720d5732b29e0b34250a8
mkdir -p "$archives"
for component in rustc cargo rust-std; do
  case "$component" in
    rustc) digest=89551c0ba1cc6d0312aebc4a6cafe4497223217ea8e87c81f6afbe127dfaeeb6 ;;
    cargo) digest=17a4410a27bf7dad4765f3809265c225f25f8b009da3d4b76cd0927acdae04b5 ;;
    rust-std) digest=c36777aec17d617f85f94b7cb87bdd4270eeca30ef38c6f686809d163c881609 ;;
  esac
  name="$component-1.90.0-aarch64-apple-darwin"
  archive="$archives/$name.tar.xz"
  if [ ! -e "$archive" ]; then
    curl --fail --location --output "$archive" "https://static.rust-lang.org/dist/$name.tar.xz"
  fi
  actual=$(shasum -a 256 "$archive" | cut -d ' ' -f 1)
  test "$actual" = "$digest"
  installed_component=$component
  if [ "$component" = rust-std ]; then installed_component=rust-std-aarch64-apple-darwin; fi
  if ! grep -Fxq "$installed_component" "$prefix/lib/rustlib/components" 2>/dev/null; then
    if [ ! -d "$archives/$name" ]; then tar -xJf "$archive" -C "$archives"; fi
    "$archives/$name/install.sh" --prefix="$prefix" --disable-ldconfig
  fi
done
if [ ! -e "$source_dir" ]; then
  git -c gc.auto=0 clone --no-checkout https://github.com/gfx-rs/wgpu-native.git "$source_dir"
  git -C "$source_dir" checkout --detach "$revision"
fi
test "$(git -C "$source_dir" rev-parse HEAD)" = "$revision"
test -z "$(git -C "$source_dir" status --porcelain)"
git -C "$source_dir" submodule update --init --recursive
export PATH="$prefix/bin:$PATH"
export CARGO_HOME="$repo/build/cache/cargo-wgsl"
export CARGO_BUILD_JOBS=1
export WGPU_NATIVE_VERSION=27.0.4.0
# In this pinned release the outer feature omits the required core feature.
cargo build --manifest-path "$source_dir/Cargo.toml" --release --locked \
  --no-default-features --features wgsl,vulkan-portability,wgc/vulkan-portability
shasum -a 256 "$source_dir/target/release/libwgpu_native.dylib"
