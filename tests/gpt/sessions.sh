#!/usr/bin/env bash
# Runs host sessions that call each gpt.wasm function that takes or holds arrays,
# release the result and the inputs, and check that every allocation was freed.
# Usage: tests/gpt/sessions.sh [path/to/gpt.wasm]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
wasm=${1:-$root/build/gpt/gpt.wasm}
host=$root/build/tools/leanexe-wasmtime-host
failed=0

# session NAME "LENGTHS" "SCALARS": allocates one zero-filled array per length,
# calls NAME with the arrays and then the scalar arguments (u64:N or f64:BITS),
# and releases the result and the arrays.
session() {
  local name=$1 lengths=$2 scalars=$3 script="" i=1 n
  for n in $lengths; do
    script+="alloc $i $((8 * (n + 1)))"$'\n'"write-u64 $i 0 $n"$'\n'
    i=$((i + 1))
  done
  for ((j = 1; j < i; j++)); do script+="arg-ptr $j"$'\n'; done
  for s in $scalars; do script+="arg-${s%%:*} ${s#*:}"$'\n'; done
  script+="call $name 1"$'\n'"arg-u64 result:0"$'\n'"call release 0"$'\n'
  for ((j = 1; j < i; j++)); do script+="arg-ptr $j"$'\n'"call release 0"$'\n'; done
  script+="stats"$'\n'
  local stats
  stats=$(printf '%s' "$script" | "$host" session "$wasm" | tail -1)
  read -r _ allocs retains releases frees <<<"$stats"
  if [ "$allocs" = "$releases" ] && [ "$allocs" = "$frees" ] && [ "$retains" = 0 ]; then
    echo "$name: $allocs allocations, $releases releases, $frees frees"
  else
    echo "fail: $name: $stats"
    failed=$((failed + 1))
  fi
}

eps=f64:4532020583610935537  # 1e-5
# t = 2 rows, nh = 2 heads of width dh = 1, so d = 2; f = 3; vocab = 3.
session matVec2 "4 4 2" "u64:2 u64:2"
session softmax "4" ""
session layerNorm "4 4 4" "$eps"
session layerNormRows "4 2 2" "u64:2 u64:2 $eps"
session softmaxRows "8" "u64:2 u64:2"
session mlp "4 6 3 6 2" "u64:2 u64:2 u64:3"
session attention "4 4 2 4 2 4 2 4 2" "u64:2 u64:2 u64:1"
layer="2 2 4 2 4 2 4 2 4 2 2 2 6 3 6 2"
session block "4 $layer" "u64:2 u64:2 u64:1 u64:3 $eps"
# Two layers of stacked weights; `blockAt` runs layer 1.
stacked="4 4 8 4 8 4 8 4 8 4 4 4 12 6 12 4"
session blockAt "4 $stacked" "u64:1 u64:2 u64:2 u64:1 u64:3 $eps"
session forward "2 6 4 $stacked 2 2" "u64:2 u64:2 u64:2 u64:1 u64:3 u64:3 $eps"
[ "$failed" -eq 0 ]
