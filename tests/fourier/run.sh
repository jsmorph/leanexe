#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
out=${FOURIER_TEST_OUT:-$root/build/fourier}
canonical=$root/build/verified/fft.wasm
fft=${FOURIER_FFT_WASM:-$canonical}
direct=${FOURIER_DFT_WASM:-$root/build/verified/fourier.wasm}
lock_timeout=${LEANRUN_LOCK_TIMEOUT:-1200}
host=${LEANEXE_WASMTIME_HOST:-$root/build/tools/leanexe-wasmtime-host}
wasm_tools=${WASM_TOOLS:-wasm-tools}
cd "$root"
mkdir -p "$out"
mode=${1:-all}
case "$mode" in
  all|prepare|proof|cases|accuracy|runtime|benchmark) ;;
  *) printf 'usage: tests/fourier/run.sh [all|prepare|proof|cases|accuracy|runtime|benchmark]\n' >&2; exit 2 ;;
esac
if [ "$mode" = proof ] || [ "$mode" = prepare ] || [ "$mode" = all ]; then
  tools/leanrun --timeout 30m --lock-timeout "$lock_timeout" lake build Verified.Examples.FFTBytes
  mkdir -p "$(dirname "$canonical")"
  tools/leanrun --timeout 10m --lock-timeout "$lock_timeout" lake env lean --run tools/Emit.lean \
    Verified.Examples.FFTProgram Verified.Examples.FFT.compiled.module "$canonical"
  reports=$(tools/leanrun --timeout 10m --lock-timeout "$lock_timeout" lake env lean \
    Verified/Examples/FFTFile.lean 2>&1) || {
    printf '%s\n' "$reports"
    printf 'fail: FFTFile does not check against %s\n' "$canonical" >&2
    exit 1
  }
  permitted=$(grep -c 'depends on axioms: \[propext, Classical\.choice, Quot\.sound\]$' \
    <<<"$reports" || true)
  total=$(grep -cE 'depends on axioms:|does not depend on any axioms' <<<"$reports" || true)
  if [ "$permitted" -ne 2 ] || [ "$total" -ne 2 ]; then
    printf '%s\n' "$reports"
    printf 'fail: FFTFile must report exactly two theorems with the three permitted axioms\n' >&2
    exit 1
  fi
  printf '%s\n' "$reports"
  if [ ! "$fft" -ef "$canonical" ]; then
    mkdir -p "$(dirname "$fft")"
    cp "$canonical" "$fft"
  fi
fi
if [ "$mode" = cases ] || [ "$mode" = prepare ] || [ "$mode" = all ]; then
  tools/leanrun --timeout 10m --lock-timeout "$lock_timeout" lake env lean --run \
    Verified/Examples/FFTCases.lean >"$out/cases.txt"
fi
if [ "$mode" = accuracy ] || [ "$mode" = prepare ] || [ "$mode" = all ]; then
  tools/leanrun --timeout 10m --lock-timeout "$lock_timeout" lake env lean Verified/Examples/FFTAccuracy.lean
fi
if [ "$mode" = runtime ] || [ "$mode" = all ]; then
  "$wasm_tools" validate "$fft"
  count=0
  while IFS='|' read -r name arg expected; do
    got=$("$host" call-stats "$fft" "$name" array-u64 "$arg")
    result=$(sed '$d' <<<"$got")
    read -r _ allocs frees < <(tail -n 1 <<<"$got")
    if [ "$result" != "$expected" ] || [ "$((allocs - frees))" -ne 2 ]; then
      printf 'fail: %s %s\nresult: %s\nexpected: %s\nlive allocations: %s\n' \
        "$name" "$arg" "$result" "$expected" "$((allocs - frees))" >&2
      exit 1
    fi
    count=$((count + 1))
  done <"$out/cases.txt"
  [ "$count" -gt 0 ]
  printf 'FFT compiler cases: %s passed\n' "$count"
fi
if [ "$mode" = benchmark ]; then
  "$wasm_tools" validate "$fft"
  "$wasm_tools" validate "$direct"
  printf 'function float_count median_ns allocations_per_call\n'
  for p in 4 6 8 10 12 14 16 18; do
    n=$((1 << p))
    repetitions=$((65536 / n))
    [ "$repetitions" -gt 0 ] || repetitions=1
    "$host" bench-array "$fft" fft "$((2 * n))" "$repetitions"
    if [ "$p" -le 12 ]; then
      "$host" bench-array "$direct" dft "$((2 * n))" 1
    fi
  done
fi
