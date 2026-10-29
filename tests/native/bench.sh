#!/usr/bin/env bash
# Times seven workloads of the verified corpus in two forms: translated to C and compiled with
# CompCert, and run as WebAssembly by Wasmtime through build/tools/leanexe-wasmtime-host.  Both
# hosts take `bench SECONDS MAX FUNC RESULT [ARG...]`, which warms up with one call, then repeats
# the call until SECONDS have passed or MAX calls have run, placing the arguments again before
# each call and timing only the call.  Each measurement is a pair, one run of each form, both
# pinned with taskset to the same core of the kind with the highest clock rate; the pairs
# alternate which form runs first.  A pair runs only when the machine is idle: no lean or lake
# process runs and the one-minute load average is below 1.  The script checks that before and
# after each pair, discards a pair that fails the check after it ran, and waits up to
# BENCH_WAIT seconds, 86400 by default, for the machine to become idle before giving up.  It
# writes the inputs, the programs, the environment, each pair's results, and a summary with the
# median and interquartile range of the time per call into build/native/bench.
#
#
# The time of the native form also depends on where its code lies, since CompCert aligns a
# function to 4 bytes on AArch64.  `--placements` measures the native form at sixteen
# placements: it links each program again after an object of K bytes of padding, for
# K = 4, 8, ..., 60, which moves the program's code by K bytes, takes the program of the pairs as
# K = 0, and runs each of the sixteen binaries BENCH_ROUNDS (2) times, between the same idle
# checks as a pair.  The summary then adds, per workload, the mean time per call over the
# placements and the means of the fastest and the slowest placement, next to the median of the
# pairs.  A comparison of two builds of the translator rests on these means (the section on the
# benchmark method in docs/native-translator.md); the default, without the sweep, compares one
# build with Wasmtime.
#
# BENCH_PAIRS (11) is the number of pairs per workload, BENCH_SECONDS (1) the timed period of a
# run, and BENCH_CORE the core, when set.  `--test` runs one short pair per workload, and with
# `--placements` one short run per placement, without waiting for the machine to become idle, to
# check the commands; its results are not measurements.  CCOMP, CLIGHTGEN, and CCOMP_STDLIB are
# as for tests/native/run.sh.  LEANRUN_MEMORY_HIGH is the memory limit of each step that runs
# under tools/leanrun, 8G unless the caller sets it, since tools/Emit.lean loads a module as
# tools/Subset.lean does.
# Usage: tests/native/bench.sh [--test] [--placements]
set -euo pipefail
export LEANRUN_MEMORY_HIGH=${LEANRUN_MEMORY_HIGH:-8G}
test_run=0
placements=0
for arg in "$@"; do
  case $arg in
    --test) test_run=1 ;;
    --placements) placements=1 ;;
    *)
      echo "usage: tests/native/bench.sh [--test] [--placements]" >&2
      exit 2
      ;;
  esac
done
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
pairs=${BENCH_PAIRS:-11}
seconds=${BENCH_SECONDS:-1}
wait_limit=${BENCH_WAIT:-86400}
rounds=${BENCH_ROUNDS:-2}
shifts="4 8 12 16 20 24 28 32 36 40 44 48 52 56 60"
if [ "$test_run" -eq 1 ]; then
  pairs=1
  seconds=0.05
  rounds=1
fi
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$root/build/native/bench
host=$root/build/tools/leanexe-wasmtime-host
cd "$root"
if [ ! -x "$host" ] || [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  echo "fail: $host is missing or older than tools/wasmtime-host.c; build it with tools/build-wasmtime-host.sh" >&2
  exit 1
fi
tools/leanrun --timeout 12h lake --log-level error build native-verified
mkdir -p "$out/inputs" "$out/native" "$out/wasm"

# The inputs (tests/native/bench_inputs.py).
uv run tests/native/bench_inputs.py "$out/inputs"

# The programs.  The native host is tools/native-host.c, compiled with -Dmain=host_main, and
# tools/native-bench.c, which adds `bench`.
"$ccomp" "${stdlib[@]}" -I "$root/tools" -Dmain=host_main -c "$root/tools/native-host.c" \
  -o "$out/native/host.o"
for name in sha256 sha3 crc libsort euler gpt32; do
  line=$(grep ":$name\$" tests/verified/modules.txt)
  module=${line%%:*}
  rest=${line#*:}
  constant=${rest%%:*}
  CLIGHTGEN=$clightgen CCOMP=$ccomp tools/leanrun --timeout 10m lake env \
    .lake/build/bin/native-verified build "$module" "$constant" "$name" "$out/native"
  "$ccomp" "${stdlib[@]}" -I "$root/tools" -o "$out/native/$name" "$out/native/$name.o" \
    "$out/native/${name}_glue.c" "$root/tools/native-bench.c" "$out/native/host.o"
  tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean "$module" "$constant" \
    "$out/wasm/$name.wasm"
done

# The programs moved by K bytes: the same link after an object that holds K bytes of padding in
# its text section, which the linker places first.
if [ "$placements" -eq 1 ]; then
  mkdir -p "$out/native/placements"
  for k in $shifts; do
    printf '\t.text\n\t.balign 4\n\t.space %d\n' "$k" >"$out/native/placements/pad$k.s"
    "$ccomp" -c "$out/native/placements/pad$k.s" -o "$out/native/placements/pad$k.o"
    for name in sha256 sha3 crc libsort euler gpt32; do
      "$ccomp" "${stdlib[@]}" -I "$root/tools" -o "$out/native/placements/$name-$k" \
        "$out/native/placements/pad$k.o" "$out/native/$name.o" "$out/native/${name}_glue.c" \
        "$root/tools/native-bench.c" "$out/native/host.o"
    done
  done
fi

# The core: the highest-numbered online core of the highest maximum clock rate.
online_cores() {
  local d c
  for d in /sys/devices/system/cpu/cpu[0-9]*; do
    c=${d##*/cpu}
    if [ -f "$d/online" ] && [ "$(cat "$d/online")" != 1 ]; then continue; fi
    if [ -r "$d/cpufreq/cpuinfo_max_freq" ]; then echo "$c $(cat "$d/cpufreq/cpuinfo_max_freq")"; fi
  done
}
if [ -n "${BENCH_CORE:-}" ]; then
  core=$BENCH_CORE
else
  core=$(online_cores | sort -k2,2n -k1,1n | tail -1 | cut -d' ' -f1)
fi

stamp=$(date -u +%Y%m%dT%H%M%SZ)
if [ "$test_run" -eq 1 ]; then stamp=$stamp-test; fi
run=$out/$stamp
mkdir -p "$run"
{
  echo "architecture: $(uname -m)"
  echo "core: $core, maximum clock $(( $(cat /sys/devices/system/cpu/cpu$core/cpufreq/cpuinfo_max_freq) / 1000 )) MHz"
  echo "frequency governor: $(cat /sys/devices/system/cpu/cpu$core/cpufreq/scaling_governor)"
  echo "ccomp: $("$ccomp" -version | head -1), from the 3.18 sources; options: -fno-common -c for the translation, -stdlib and -I to link"
  echo "wasmtime: C API $(ls build/tools/wasmtime 2>/dev/null | sed -n 's/^wasmtime-v\([0-9.]*\)-.*-c-api$/\1/p' | head -1), Cranelift, NaN canonicalization on"
  echo "pairs: $pairs, timed period: $seconds s"
  if [ "$placements" -eq 1 ]; then echo "placements: 16, runs per placement: $rounds"; fi
} >"$run/environment.txt"

idle() {
  local lean
  lean=$(ps -eo comm= | grep -cx -E 'lean|lake' || true)
  [ "$lean" -eq 0 ] && awk '{ exit !($1 < 1) }' /proc/loadavg
}

wait_idle() {
  local start=$SECONDS
  until idle; do
    if [ $((SECONDS - start)) -ge "$wait_limit" ]; then
      echo "fail: the machine was not idle within $wait_limit seconds" >&2
      exit 3
    fi
    sleep 60
  done
}

# name|program|export|result|max|arguments
workloads="sha256|sha256|sha256|list:i64,i64,i64,i64|100|file-u64:$out/inputs/words-1m.bin i64:1048576
sha3|sha3|sha3_256|list:i64,i64,i64,i64|100|file-u64:$out/inputs/words-1m.bin i64:1048576
crc32|crc|crc32|i64|100|file-u64:$out/inputs/words-1m.bin i64:1048576
sort|libsort|sortInsert|array-u64|100|file-u64:$out/inputs/words-4k.bin
euler|euler|solve|array-u64|100|i64:32
linear32|gpt32|linear32|array-u64|30|file-u64:$out/inputs/x-768.bin file-u64:$out/inputs/w-768x768.bin file-u64:$out/inputs/b-768.bin i64:768 i64:768
layernorm32|gpt32|layerNorm32|array-u64|100|file-u64:$out/inputs/x-768.bin file-u64:$out/inputs/g-768.bin file-u64:$out/inputs/b-768.bin i64:768 f32:1145044992"

results=$run/results.tsv
printf 'workload\tpair\tform\tcalls\tnanoseconds\n' >"$results"
discarded=0
while IFS='|' read -r name program export result max arguments; do
  read -ra argv <<<"$arguments"
  i=1
  while [ "$i" -le "$pairs" ]; do
    if [ "$test_run" -eq 0 ]; then wait_idle; fi
    if [ $((i % 2)) -eq 1 ]; then forms="native wasm"; else forms="wasm native"; fi
    for form in $forms; do
      if [ "$form" = native ]; then
        taskset -c "$core" "$out/native/$program" bench "$seconds" "$max" "$export" "$result" \
          "${argv[@]}" >"$run/$name-$i-native.out"
      else
        taskset -c "$core" "$host" bench "$out/wasm/$program.wasm" "$seconds" "$max" "$export" \
          "$result" "${argv[@]}" >"$run/$name-$i-wasm.out"
      fi
    done
    if [ "$test_run" -eq 0 ] && ! idle; then
      discarded=$((discarded + 1))
      continue
    fi
    if ! cmp -s <(grep -v '^bench \|^init ' "$run/$name-$i-native.out") \
        <(grep -v '^bench \|^init ' "$run/$name-$i-wasm.out"); then
      echo "fail: $name: the two forms give different results" >&2
      exit 1
    fi
    for form in native wasm; do
      read -r _ calls ns < <(grep '^bench ' "$run/$name-$i-$form.out")
      printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$i" "$form" "$calls" "$ns" >>"$results"
    done
    i=$((i + 1))
  done
done <<<"$workloads"

# The sweep: each placement's binary per round, the rounds in alternating order of K, each run
# compared with the result of the first pair.
sweep=$run/placements.tsv
discarded_runs=0
if [ "$placements" -eq 1 ]; then
  printf 'workload\tround\tshift\tcalls\tnanoseconds\n' >"$sweep"
  while IFS='|' read -r name program export result max arguments; do
    read -ra argv <<<"$arguments"
    for round in $(seq 1 "$rounds"); do
      order="0 $shifts"
      if [ $((round % 2)) -eq 0 ]; then order=$(echo "$order" | tr ' ' '\n' | tac | tr '\n' ' '); fi
      for k in $order; do
        if [ "$k" -eq 0 ]; then binary=$out/native/$program; else binary=$out/native/placements/$program-$k; fi
        output=$run/$name-placement-$k-$round.out
        while :; do
          if [ "$test_run" -eq 0 ]; then wait_idle; fi
          taskset -c "$core" "$binary" bench "$seconds" "$max" "$export" "$result" "${argv[@]}" \
            >"$output"
          if [ "$test_run" -eq 1 ] || idle; then break; fi
          discarded_runs=$((discarded_runs + 1))
        done
        if ! cmp -s <(grep -v '^bench \|^init ' "$output") \
            <(grep -v '^bench \|^init ' "$run/$name-1-native.out"); then
          echo "fail: $name: the program moved by $k bytes gives a different result" >&2
          exit 1
        fi
        read -r _ calls ns < <(grep '^bench ' "$output")
        printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$round" "$k" "$calls" "$ns" >>"$sweep"
      done
    done
  done <<<"$workloads"
fi

# The summary: per workload and form, the median and the quartiles of the time per call over
# the pairs, and the ratio of the medians.
awk -F'\t' 'NR > 1 { print $1 "\t" $3 "\t" $5 / $4 }' "$results" | sort -t$'\t' -k1,1 -k2,2 -k3,3g |
  awk -F'\t' '
    function q(a, n, p,   h, l) { h = (n - 1) * p + 1; l = int(h); return a[l] + (h - l) * (a[l + 1 < n ? l + 1 : n] - a[l]) }
    function flush() {
      if (n == 0) return
      med[key] = q(v, n, 0.5)
      printf "%s\t%s\t%.0f\t%.0f\t%.0f\n", w, f, med[key], q(v, n, 0.25), q(v, n, 0.75)
      n = 0
    }
    { if ($1 "\t" $2 != key) { flush(); key = $1 "\t" $2; w = $1; f = $2 } v[++n] = $3 }
    END { flush() }' >"$run/summary.part"
{
  printf 'workload\tform\tmedian ns per call\tfirst quartile\tthird quartile\n'
  cat "$run/summary.part"
  echo
  printf 'workload\tWasmtime median / native median\n'
  awk -F'\t' '{ m[$1 "\t" $2] = $3; w[$1] = 1 } END { for (k in w) printf "%s\t%.2f\n", k, m[k "\twasm"] / m[k "\tnative"] }' \
    "$run/summary.part" | sort
  echo
  echo "discarded pairs: $discarded"
  if [ "$placements" -eq 1 ]; then
    echo
    echo "native form at 16 placements, code moved by 0 to 60 bytes, $rounds runs each"
    printf 'workload\tform\tmean ns per call over placements\tfastest placement\tslowest placement\tmedian of pairs\n'
    awk -F'\t' '
      NR == FNR { if ($2 == "native") med[$1] = $3; next }
      FNR > 1 { key = $1 "\t" $3; s[key] += $5 / $4; c[key]++; if (!(key in seen)) { seen[key] = 1; ks[$1] = ks[$1] " " $3 }
        if (!($1 in w)) { w[$1] = 1; ord[++n] = $1 } }
      END { for (i = 1; i <= n; i++) { x = ord[i]; m = split(ks[x], k, " "); t = 0
          for (j = 1; j <= m; j++) { v = s[x "\t" k[j]] / c[x "\t" k[j]]; t += v; if (j == 1 || v < lo) lo = v; if (j == 1 || v > hi) hi = v }
          printf "%s\tnative\t%.0f\t%.0f\t%.0f\t%.0f\n", x, t / m, lo, hi, med[x] } }' \
      "$run/summary.part" "$sweep"
    echo
    echo "discarded placement runs: $discarded_runs"
  fi
} >"$run/summary.txt"
cat "$run/environment.txt" "$run/summary.txt"
