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
# BENCH_PAIRS (11) is the number of pairs per workload, BENCH_SECONDS (1) the timed period of a
# run, and BENCH_CORE the core, when set.  `--test` runs one short pair per workload without
# waiting for the machine to become idle, to check the commands; its results are not
# measurements.  CCOMP, CLIGHTGEN, and CCOMP_STDLIB are as for tests/native/run.sh.
# LEANRUN_MEMORY_HIGH is the memory limit of each step that runs under tools/leanrun, 8G unless
# the caller sets it, since tools/Emit.lean loads a module as tools/Subset.lean does.
# Usage: tests/native/bench.sh [--test]
set -euo pipefail
export LEANRUN_MEMORY_HIGH=${LEANRUN_MEMORY_HIGH:-8G}
test_run=0
if [ "$#" -eq 1 ] && [ "$1" = "--test" ]; then
  test_run=1
elif [ "$#" -ne 0 ]; then
  echo "usage: tests/native/bench.sh [--test]" >&2
  exit 2
fi
ccomp=${CCOMP:-ccomp}
clightgen=${CLIGHTGEN:-clightgen}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
pairs=${BENCH_PAIRS:-11}
seconds=${BENCH_SECONDS:-1}
wait_limit=${BENCH_WAIT:-86400}
if [ "$test_run" -eq 1 ]; then
  pairs=1
  seconds=0.05
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

# The inputs: 1 MiB of words for the hashes, 4,096 words to sort, and the vectors and the matrix
# of GPT-2's width 768 as the bits of floats in words, all from a fixed linear congruential
# sequence.
python3 - "$out/inputs" <<'EOF'
import struct, sys
d = sys.argv[1]
state = 1
def word():
    global state
    state = (state * 6364136223846793005 + 1442695040888963407) % 2**64
    return state
def floats(n):
    return [struct.unpack('<I', struct.pack('<f', (word() >> 40) / 2**23 - 1.0))[0] for _ in range(n)]
def write(name, words):
    with open(f"{d}/{name}", "wb") as f:
        f.write(b"".join(struct.pack('<Q', w) for w in words))
write("words-1m.bin", [word() for _ in range(131072)])
write("words-4k.bin", [word() for _ in range(4096)])
write("x-768.bin", floats(768))
write("g-768.bin", floats(768))
write("b-768.bin", floats(768))
write("w-768x768.bin", floats(768 * 768))
EOF

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
} >"$run/summary.txt"
cat "$run/environment.txt" "$run/summary.txt"
