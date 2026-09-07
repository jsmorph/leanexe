# Source from the repository root after tools/bootstrap-macos.sh.
# Existing versions and workspaces elsewhere on this machine are untouched.
LEANRUN_TOOLCHAIN="$PWD/build/tools/lean-4.34.0-rc2-darwin_aarch64"
LEAN_SYSROOT="$LEANRUN_TOOLCHAIN"
LEANRUN_LOCAL=1
# Approved for this project's ARM Mac sandbox on 2026-09-07.
LEANRUN_INHERIT_PRIORITY=1
LEAN_NUM_THREADS=1
WASM_TOOLS="$PWD/build/tools/wasm-tools-1.251.0-aarch64-macos/wasm-tools"
WASMTIME="$PWD/build/tools/wasmtime-v44.0.0-aarch64-macos/wasmtime"
WASMTIME_C_API="$PWD/build/tools/wasmtime-v44.0.0-aarch64-macos-c-api"
MATHLIB_CACHE_DIR="$PWD/build/cache/mathlib"
PATH="$PWD/build/tools/node-v24.13.0-darwin-arm64/bin:$LEANRUN_TOOLCHAIN/bin:$PATH"
export LEANRUN_TOOLCHAIN LEAN_SYSROOT LEANRUN_LOCAL LEANRUN_INHERIT_PRIORITY LEAN_NUM_THREADS
export WASM_TOOLS WASMTIME WASMTIME_C_API MATHLIB_CACHE_DIR PATH
