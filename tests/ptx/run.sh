#!/usr/bin/env bash
# Runs PTX kernels on an NVIDIA GPU with the text that tools/EmitPtx.lean prints, on cases whose
# expected output words native Lean computes, and compares the words.  ptxas compiles each kernel
# with `-O3 --fmad=false` for the GPU's architecture, and the script records the version of ptxas,
# the cubin's SHA-256, and its SASS in the build directory's ptx/.  Each case runs twice: from the cubin, and from the
# PTX text through the driver's compiler.
# Usage: tests/ptx/run.sh [build directory]
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
build=${1:-$root/build}
out=$build/ptx
host=$root/build/tools/leanexe-cuda-host
cuda=${CUDA_HOME:-/usr/local/cuda}
# Each kernel as MODULE:CONSTANT:NAME, where NAME.ptx receives the text of CONSTANT.
kernels=(LeanExe.PTX.AddOne:LeanExe.PTX.addOne:addOne)
mkdir -p "$out"
arch=$("$host" info | sed -n 's/^compute capability \([0-9]*\)\.\([0-9]*\)$/sm_\1\2/p')
if [ -z "$arch" ]; then
  echo "cannot read the GPU's compute capability from $host info" >&2
  exit 1
fi
(cd "$root" && tools/leanrun --timeout 20m lake --log-level error build LeanExe.PTX.Parse \
  LeanExe.PTX.AddOne)
"$cuda/bin/ptxas" --version >"$out/ptxas.version"
: >"$out/cubins.sha256"
for entry in "${kernels[@]}"; do
  IFS=: read -r module constant kernel <<<"$entry"
  (cd "$root" && tools/leanrun --timeout 10m lake env lean --run tools/EmitPtx.lean \
    "$module" "$constant" "$out/$kernel.ptx")
  "$cuda/bin/ptxas" -arch="$arch" -O3 --fmad=false "$out/$kernel.ptx" -o "$out/$kernel.cubin"
  (cd "$out" && sha256sum "$kernel.cubin") >>"$out/cubins.sha256"
  "$cuda/bin/cuobjdump" -sass "$out/$kernel.cubin" >"$out/$kernel.sass"
done
cases=$out/cases.txt
if ! (cd "$root" && tools/leanrun --timeout 10m lake env lean --run tests/ptx/Cases.lean) \
    >"$cases"; then
  cat "$cases" >&2
  exit 1
fi
status=0
for image in cubin ptx; do
  passed=0
  failed=0
  case_number=0
  failures=$out/$image.failures.txt
  : >"$failures"
  while IFS='|' read -r kernel blocks output inputs expected; do
    case_number=$((case_number + 1))
    read -ra argv <<<"$inputs"
    if result_words=$("$host" run "$out/$kernel.$image" main "$blocks" "$output" "${argv[@]}" \
        2>"$out/host.stderr.log"); then
      true
    else
      result=$?
      cat "$out/host.stderr.log" >&2
      echo "host failed: $kernel from the $image, case $case_number, status $result" >&2
      exit "$result"
    fi
    if [ "$result_words" = "$expected" ]; then
      passed=$((passed + 1))
    else
      failed=$((failed + 1))
      printf '%s|%s|%s|%s|%s|%s\n' "$case_number" "$kernel" "$blocks" "$output" "$inputs" \
        "$expected" >>"$failures"
      printf 'actual|%s\n' "$result_words" >>"$failures"
      echo "fail: $kernel from the $image, case $case_number; values in $failures"
    fi
  done <"$cases"
  echo "$arch $image: passed $passed failed $failed"
  [ "$failed" -eq 0 ] || status=1
done
exit $status
