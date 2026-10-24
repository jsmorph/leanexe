#!/bin/sh
set -eu
set -f
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
fixtures="$root/tests/wasi/reflection"
out="$root/build/wasi/reflection"
host="$root/build/tools/leanexe-wasmtime-host"
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi

tools/leanrun --timeout 10m --log build/wasi/reflection/build.log lake build Verified.Wasi.ReflectProgramCases
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Wasi.ReflectProgramCases \
  Verified.Wasi.ReflectProgramCases.callable.module "$out/callable.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Wasi.ReflectProgramCases \
  Verified.Wasi.ReflectProgramCases.command.module "$out/command.wasm"
wasm-tools validate "$out/callable.wasm"
wasm-tools validate "$out/command.wasm"

case_count=0

begin_case() {
  case_name=$1
  case_dir="$out/$case_name"
  mkdir -p "$case_dir"
  guest_stdout="$case_dir/guest.stdout"
  guest_stderr="$case_dir/guest.stderr"
  control="$case_dir/control"
  host_stdout="$case_dir/host.stdout"
  host_stderr="$case_dir/host.stderr"
  : >"$guest_stdout"
  : >"$guest_stderr"
  : >"$control"
}

run_host() {
  expected_status=$1
  shift
  observed_status=0
  timeout 30s "$host" "$@" >"$host_stdout" 2>"$host_stderr" || observed_status=$?
  if [ "$observed_status" -ne "$expected_status" ]; then
    printf '%s: expected process status %s, observed %s\n' \
      "$case_name" "$expected_status" "$observed_status" >&2
    cat "$host_stderr" >&2
    printf 'Captures: %s\n' "$case_dir" >&2
    exit 1
  fi
  case_count=$((case_count + 1))
}

compare_file() {
  if ! cmp "$1" "$2"; then
    printf '%s: expected %s, observed %s\n' "$case_name" "$1" "$2" >&2
    cat "$host_stderr" >&2
    exit 1
  fi
}

check_case() {
  compare_file "$fixtures/$1" "$control"
  compare_file "$fixtures/$2" "$guest_stdout"
  compare_file "$fixtures/$3" "$guest_stderr"
  compare_file "$fixtures/empty.bin" "$host_stdout"
  compare_file "$fixtures/empty.bin" "$host_stderr"
}

tab=$(printf '\t')
while IFS="$tab" read -r name export_name argument input expected stdout stderr; do
  begin_case "$name"
  if [ "$argument" = _ ]; then set --; else set -- "i64:$argument"; fi
  run_host 0 --wasi --stdin-file "$fixtures/$input" --stdout-file "$guest_stdout" \
    --stderr-file "$guest_stderr" --control-file "$control" \
    call "$out/callable.wasm" "$export_name" i64 "$@"
  check_case "$expected" "$stdout" "$stderr"
done <"$fixtures/calls.tsv"

while IFS="$tab" read -r name input process_status expected stdout stderr; do
  begin_case "$name"
  run_host "$process_status" --wasi --stdin-file "$fixtures/$input" \
    --stdout-file "$guest_stdout" --stderr-file "$guest_stderr" --control-file "$control" \
    run "$out/command.wasm"
  check_case "$expected" "$stdout" "$stderr"
done <"$fixtures/commands.tsv"

printf 'Reflected WASI source and encoding tests passed: %s native cases\n' "$case_count"
