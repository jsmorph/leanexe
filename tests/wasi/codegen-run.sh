#!/bin/sh
set -eu
set -f
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
fixtures="$root/tests/wasi/codegen"
out="$root/build/wasi/codegen"
host="$root/build/tools/leanexe-wasmtime-host"
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi
if [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  printf 'Native host is older than tools/wasmtime-host.c; rebuild it with tools/build-wasmtime-host.sh\n' >&2
  exit 1
fi

tools/leanrun --timeout 10m --log build/wasi/codegen/build.log lake build Verified.Examples.WasiCodegen
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiCodegen \
  Verified.Examples.WasiCodegen.callable "$out/callable.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiCodegen \
  Verified.Examples.WasiCodegen.returnedCommand "$out/returned.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiCodegen \
  Verified.Examples.WasiCodegen.exitedCommand "$out/exited.wasm"
wasm-tools validate "$out/callable.wasm"
wasm-tools validate "$out/returned.wasm"
wasm-tools validate "$out/exited.wasm"

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
  case $expected_status in
    ''|*[!0-9]*)
      printf '%s: expected status is not a decimal number: %s\n' "$case_name" "$expected_status" >&2
      exit 1 ;;
  esac
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
  compare_file "$1" "$control"
  compare_file "$fixtures/$2" "$guest_stdout"
  compare_file "$fixtures/$3" "$guest_stderr"
  compare_file "$fixtures/empty.bin" "$host_stdout"
  if [ "$4" = empty ]; then
    compare_file "$fixtures/empty.bin" "$host_stderr"
  elif [ ! -s "$host_stderr" ]; then
    printf '%s: expected a host diagnostic in %s\n' "$case_name" "$host_stderr" >&2
    exit 1
  fi
}

tab=$(printf '\t')
while IFS="$tab" read -r name export_name argument result allocations releases input stdout stderr; do
  begin_case "$name"
  if [ "$argument" = _ ]; then set --; else set -- "i64:$argument"; fi
  printf '%s\nstats %s %s\n' "$result" "$allocations" "$releases" >"$case_dir/expected.control"
  run_host 0 --wasi --stdin-file "$fixtures/$input" --stdout-file "$guest_stdout" \
    --stderr-file "$guest_stderr" --control-file "$control" \
    call-stats "$out/callable.wasm" "$export_name" i64 "$@"
  check_case "$case_dir/expected.control" "$stdout" "$stderr" empty
done <"$fixtures/calls.tsv"

while IFS="$tab" read -r name export_name argument process_status result diagnostic; do
  begin_case "$name"
  if [ "$argument" = _ ]; then set --; else set -- "i64:$argument"; fi
  if [ "$result" = error ]; then
    printf 'error\n' >"$case_dir/expected.control"
  else
    printf 'wasi-exit %s\n' "$result" >"$case_dir/expected.control"
  fi
  run_host "$process_status" --wasi --stdin-file "$fixtures/empty.bin" \
    --stdout-file "$guest_stdout" --stderr-file "$guest_stderr" --control-file "$control" \
    call "$out/callable.wasm" "$export_name" i64 "$@"
  check_case "$case_dir/expected.control" x.bin empty.bin "$diagnostic"
done <"$fixtures/exits.tsv"

while IFS="$tab" read -r name input script expected stdout stderr process_status diagnostic; do
  begin_case "$name"
  run_host "$process_status" --wasi --stdin-file "$fixtures/$input" \
    --stdout-file "$guest_stdout" --stderr-file "$guest_stderr" --control-file "$control" \
    session "$out/callable.wasm" <"$fixtures/$script"
  check_case "$fixtures/$expected" "$stdout" "$stderr" "$diagnostic"
done <"$fixtures/sessions.tsv"

while IFS="$tab" read -r name module process_status result stdout; do
  begin_case "$name"
  printf 'wasi-exit %s\n' "$result" >"$case_dir/expected.control"
  run_host "$process_status" --wasi --stdin-file "$fixtures/empty.bin" \
    --stdout-file "$guest_stdout" --stderr-file "$guest_stderr" --control-file "$control" \
    run "$out/$module.wasm"
  check_case "$case_dir/expected.control" "$stdout" empty.bin empty
done <"$fixtures/commands.tsv"

printf 'Typed WASI code-generation tests passed: %s cases\n' "$case_count"
