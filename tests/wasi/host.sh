#!/bin/sh
set -eu
set -f
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
fixtures="$root/tests/wasi/host"
out="$root/build/wasi/host"
host="$root/build/tools/leanexe-wasmtime-host"
bytes="$root/build/wasi/bytes.wasm"
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi
if [ ! -f "$bytes" ]; then
  printf 'Missing pure byte module: %s\n' "$bytes" >&2
  exit 1
fi

while IFS= read -r module; do
  wasm-tools parse "$fixtures/$module.wat" -o "$out/$module.wasm"
  wasm-tools validate "$out/$module.wasm"
done <"$fixtures/modules.txt"

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
  compare_file "$fixtures/$4" "$host_stdout"
  if [ "$5" = empty ]; then
    compare_file "$fixtures/empty.bin" "$host_stderr"
  elif [ ! -s "$host_stderr" ]; then
    printf '%s: expected a host diagnostic in %s\n' "$case_name" "$host_stderr" >&2
    exit 1
  fi
}

begin_case call-binary
run_host 0 --wasi --stdin-file "$fixtures/input.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  call "$out/streams.wasm" echo slots:5
check_case echo.control input.bin empty.bin empty.bin empty

begin_case call-stats
run_host 0 --wasi --stdin-file "$fixtures/input.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  call-stats "$out/streams.wasm" echo slots:5
check_case echo-stats.control input.bin empty.bin empty.bin empty

begin_case stderr-binary
run_host 0 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  call "$out/streams.wasm" stderr slots:2
check_case stderr.control empty.bin stderr.bin empty.bin empty

begin_case eof
run_host 0 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  call "$out/streams.wasm" echo slots:5
check_case eof.control empty.bin empty.bin empty.bin empty

begin_case zero-transfers
run_host 0 --wasi --stdin-file "$fixtures/input.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  call "$out/streams.wasm" zero slots:4
check_case zero.control empty.bin empty.bin empty.bin empty

begin_case script
run_host 0 --wasi --stdin-file "$fixtures/input.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  script "$out/streams.wasm" <"$fixtures/script.txt"
check_case script.control input.bin empty.bin empty.bin empty

begin_case session
run_host 0 --wasi --stdin-file "$fixtures/session-input.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  session "$out/streams.wasm" <"$fixtures/session.txt"
check_case session.control session-input.bin stderr.bin empty.bin empty

begin_case default-control
run_host 0 --wasi --stdin-file "$fixtures/input.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" call-stats "$out/streams.wasm" echo slots:5
check_case empty.bin input.bin empty.bin echo-stats.control empty

begin_case inherited-guest-stdout
run_host 0 --wasi --stdin-file "$fixtures/input.bin" --stderr-file "$guest_stderr" \
  --control-file "$control" call "$out/streams.wasm" echo slots:5
check_case echo.control empty.bin empty.bin input.bin empty

begin_case run-return
run_host 0 --stdin-file "$fixtures/input.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" run "$out/streams.wasm"
check_case return.control input.bin stderr.bin empty.bin empty

begin_case run-inherited-stdio
run_host 0 run "$out/streams.wasm" <"$fixtures/input.bin"
compare_file "$fixtures/input.bin" "$host_stdout"
compare_file "$fixtures/stderr.bin" "$host_stderr"
compare_file "$fixtures/empty.bin" "$control"

begin_case session-exit
run_host 0 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  session "$out/lifecycle.wasm" <"$fixtures/session-exit.txt"
check_case session-exit.control before.bin empty.bin empty.bin empty

begin_case session-reject
run_host 1 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  session "$out/lifecycle.wasm" <"$fixtures/session-reject.txt"
check_case session-reject.control before.bin empty.bin empty.bin diagnostic

begin_case script-exit
run_host 0 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  script "$out/lifecycle.wasm" <"$fixtures/script-exit.txt"
check_case exit-0.control empty.bin empty.bin empty.bin empty

begin_case script-reject
run_host 1 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  script "$out/lifecycle.wasm" <"$fixtures/script-reject.txt"
check_case error.control empty.bin empty.bin empty.bin diagnostic

begin_case session-trap
run_host 2 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  session "$out/lifecycle.wasm" <"$fixtures/session-trap.txt"
check_case session-trap.control before.bin empty.bin empty.bin diagnostic

begin_case engine-error
run_host 1 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$control" \
  call "$out/lifecycle.wasm" exit slots:0
check_case error.control empty.bin empty.bin empty.bin diagnostic

tab=$(printf '\t')
while IFS="$tab" read -r name scalar_count final_argument; do
  begin_case "$name"
  set --
  index=0
  while [ "$index" -lt "$scalar_count" ]; do
    set -- "$@" i64:0
    index=$((index + 1))
  done
  if [ "$final_argument" != _ ]; then set -- "$@" "$final_argument"; fi
  run_host 1 call "$bytes" identity bytes "$@"
  check_case empty.bin empty.bin empty.bin empty.bin diagnostic
  compare_file "$fixtures/argument-limit.err" "$host_stderr"
done <"$fixtures/argument-limits.tsv"

for command in write-u64 write-bytes; do
  begin_case "$command-overflow"
  run_host 1 script "$bytes" <"$fixtures/$command-overflow.txt"
  check_case empty.bin empty.bin empty.bin empty.bin diagnostic
  compare_file "$fixtures/pointer-overflow.err" "$host_stderr"
done

while IFS="$tab" read -r module request process_status diagnostic; do
  begin_case "run-$module-$request"
  run_host "$process_status" --stdin-file "$fixtures/empty.bin" \
    --stdout-file "$guest_stdout" --stderr-file "$guest_stderr" \
    --control-file "$control" run "$out/$module.wasm"
  check_case "$module.control" empty.bin empty.bin empty.bin "$diagnostic"
done <"$fixtures/exits.tsv"

for stream in stdin stdout stderr; do
  begin_case "missing-$stream-file"
  missing_path="$case_dir/missing/stream"
  stdin_path="$fixtures/empty.bin"
  stdout_path="$guest_stdout"
  stderr_path="$guest_stderr"
  case "$stream" in
    stdin) stdin_path=$missing_path ;;
    stdout) stdout_path=$missing_path ;;
    stderr) stderr_path=$missing_path ;;
  esac
  run_host 1 --wasi --stdin-file "$stdin_path" --stdout-file "$stdout_path" \
    --stderr-file "$stderr_path" --control-file "$control" \
    call "$out/streams.wasm" echo slots:5
  check_case empty.bin empty.bin empty.bin empty.bin diagnostic
  case "$(cat "$host_stderr")" in
    *"$missing_path"*) ;;
    *) printf '%s: diagnostic omits the failed path\n' "$case_name" >&2; exit 1 ;;
  esac
done

begin_case missing-control-file
missing_path="$case_dir/missing/control"
run_host 1 --wasi --stdin-file "$fixtures/empty.bin" --stdout-file "$guest_stdout" \
  --stderr-file "$guest_stderr" --control-file "$missing_path" \
  call "$out/streams.wasm" echo slots:5
check_case empty.bin empty.bin empty.bin empty.bin diagnostic
case "$(cat "$host_stderr")" in
  *"$missing_path"*) ;;
  *) printf '%s: diagnostic omits the failed path\n' "$case_name" >&2; exit 1 ;;
esac

begin_case missing-session-guest-input
run_host 1 --wasi --stdout-file "$guest_stdout" --stderr-file "$guest_stderr" \
  --control-file "$control" session "$out/streams.wasm" <"$fixtures/session.txt"
check_case empty.bin empty.bin empty.bin empty.bin diagnostic

begin_case missing-output-isolation
run_host 1 --wasi --stdin-file "$fixtures/input.bin" --stderr-file "$guest_stderr" \
  call "$out/streams.wasm" echo slots:5
check_case empty.bin empty.bin empty.bin empty.bin diagnostic

native_count=$case_count
pure_count=0
while IFS="$tab" read -r export_name kind arguments expected allocations releases; do
  begin_case "pure-$pure_count-$export_name"
  if [ "$expected" = _ ]; then expected=; fi
  if [ "$arguments" = _ ]; then set --; else set -- $arguments; fi
  run_host 0 call-stats "$bytes" "$export_name" "$kind" "$@"
  printf '%s\nstats %s %s\n' "$expected" "$allocations" "$releases" >"$case_dir/expected"
  compare_file "$case_dir/expected" "$host_stdout"
  compare_file "$fixtures/empty.bin" "$host_stderr"
  pure_count=$((pure_count + 1))
done <"$root/tests/wasi/bytes.tsv"

printf 'WASI native host tests passed: %s cases\n' "$native_count"
printf 'Pure CLI compatibility tests passed: %s byte cases\n' "$pure_count"
