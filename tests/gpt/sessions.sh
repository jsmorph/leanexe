#!/usr/bin/env bash
# Runs host sessions that call each gpt.wasm function that takes or holds arrays,
# release the result and the inputs, and check that every allocation was freed.
# Usage: tests/gpt/sessions.sh [path/to/gpt.wasm]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
wasm=${1:-$root/build/gpt/gpt.wasm}
host=$root/build/tools/leanexe-wasmtime-host
failed=0

# session NAME "LENGTHS" "SCALARS" [CONSUMED]: allocates one zero-filled array per
# length, calls NAME with the arrays and then the scalar arguments (u64:N or f64:BITS),
# and releases the result and the arrays other than the first CONSUMED, which the call
# consumes.
session() {
  local name=$1 lengths=$2 scalars=$3 consumed=${4:-0} script="" i=1 n
  for n in $lengths; do
    script+="alloc $i $((8 * (n + 1)))"$'\n'"write-u64 $i 0 $n"$'\n'
    i=$((i + 1))
  done
  for ((j = 1; j < i; j++)); do script+="arg-ptr $j"$'\n'; done
  for s in $scalars; do script+="arg-${s%%:*} ${s#*:}"$'\n'; done
  script+="call $name 1"$'\n'"arg-u64 result:0"$'\n'"call release 0"$'\n'
  for ((j = 1 + consumed; j < i; j++)); do script+="arg-ptr $j"$'\n'"call release 0"$'\n'; done
  script+="stats"$'\n'
  local stats
  stats=$(printf '%s' "$script" | "$host" session "$wasm" | tail -1)
  read -r _ allocs frees <<<"$stats"
  if [ "$allocs" = "$frees" ]; then
    echo "$name: $allocs allocations, $frees frees"
  else
    echo "fail: $name: $stats"
    failed=$((failed + 1))
  fi
}

# growth N B: appends a block of B words to a cache N times with appendBlock, which
# consumes each old cache, and checks that memory stays below eight times the final
# cache plus 1 MiB and that every allocation was freed.  An allocator that cannot reuse
# the freed blocks, or an append that copies on every call, needs far more.
growth() {
  local n=$1 b=$2 script="" i old new
  script+="alloc 1 $((8 * (b + 1)))"$'\n'"write-u64 1 0 $b"$'\n'
  script+="alloc 2 8"$'\n'"write-u64 2 0 0"$'\n'
  for ((i = 0; i < n; i++)); do
    old=$((2 + i % 2))
    new=$((3 - i % 2))
    script+="arg-ptr $old"$'\n'"arg-ptr 1"$'\n'"call appendBlock 1"$'\n'"keep $new result:0"$'\n'
  done
  script+="memory-size"$'\n'"arg-ptr $((2 + n % 2))"$'\n'"call release 0"$'\n'
  script+="arg-ptr 1"$'\n'"call release 0"$'\n'"stats"$'\n'
  local out size stats cache=$((8 * (n * b + 1)))
  out=$(printf '%s' "$script" | "$host" session "$wasm")
  size=$(grep '^memory-size' <<<"$out" | cut -d' ' -f2)
  stats=$(tail -1 <<<"$out")
  read -r _ allocs frees <<<"$stats"
  if [ "$size" -le $((8 * cache + 1048576)) ] && [ "$allocs" = "$frees" ]; then
    echo "growth: $n appends of $b words, memory $size bytes, final cache $cache bytes, $frees frees"
  else
    echo "fail: growth: memory $size bytes, final cache $cache bytes, $stats"
    failed=$((failed + 1))
  fi
}

eps=f64:4532020583610935537  # 1e-5
# t = 2 rows, nh = 2 heads of width dh = 1, so d = 2; f = 3; vocab = 3.
session matVec2 "4 4 2" "u64:2 u64:2"
session softmax "4" ""
session layerNorm "4 4 4" "$eps"
session layerNormRows "4 2 2" "u64:0 u64:2 u64:2 $eps"
session softmaxRows "8" "u64:2 u64:2"
session mlp "4 6 3 6 2" "u64:0 u64:2 u64:2 u64:3"
session attention "4 4 2 4 2 4 2 4 2" "u64:0 u64:2 u64:2 u64:1"
# Two layers of stacked weights; `block` runs layer 1.
stacked="4 4 8 4 8 4 8 4 8 4 4 4 12 6 12 4"
session block "4 $stacked" "u64:1 u64:2 u64:2 u64:1 u64:3 $eps"
session forward "2 6 4 $stacked 2 2" "u64:2 u64:2 u64:2 u64:1 u64:3 u64:3 $eps"
# A step from an empty cache, and the scores of a cache of one block of (2 · 2 + 1) · 2.
session step "0 6 4 $stacked" "u64:1 u64:2 u64:2 u64:1 u64:3 $eps" 1
session scores "10 6 2 2" "u64:2 u64:2 u64:1 u64:3 $eps"
growth 256 1000
[ "$failed" -eq 0 ]
