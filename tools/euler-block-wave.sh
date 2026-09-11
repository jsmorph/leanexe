#!/usr/bin/env bash
set -euo pipefail
worker=$1
cache=$2
mode=$3
mesh=$4
input=$5
output=$6
ratio=$7
pids=()
for block in {0..23}; do
    "$worker" "$cache" "$mode" "$mesh" "$block" "$input" "$output" "$ratio" &
    pids+=("$!")
done
status=0
for pid in "${pids[@]}"; do
    if wait "$pid"; then :; else status=1; fi
done
exit "$status"
