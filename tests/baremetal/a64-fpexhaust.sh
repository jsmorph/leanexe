#!/usr/bin/env bash
# The exhaustive test of the single-precision forms of LeanExe/A64/Machine.lean against QEMU and
# the processor (tests/TestSupport/A64/FpExhaust.lean).  It builds a64-fpexhaust, writes the arm64
# Image of the cases CASES, every case unless set, over SAMPLE chunks of 2^16 words of each case
# spread over the words, or over every chunk when SAMPLE is 0, computes the digests of Talos's
# results with TASKS parallel tasks, 4 unless set, checks QEMU's loading of the Image with
# tests/baremetal/a64-loadcheck.sh under each accelerator that the platforms use, and runs it on
# QEMU's virt machine with 1 GiB of RAM on every PLATFORM at once: tcg, under which QEMU emulates a
# Cortex-A57, kvm, under KVM on the host's processor, or kvm:N, under KVM pinned with taskset to
# processor N.  With SAMPLE other than 0 it also computes the digests of the model's runs of the
# cases' code and requires them to equal Talos's.  Each run must end within TIMEOUT seconds, 7200
# unless set, with QEMU's status 0, and a64-fpexhaust check then compares every chunk's digest of
# the UART output with Talos's and writes each case's counts and every differing chunk to
# OUT/PLATFORM.check, with a colon in PLATFORM written as a hyphen.  The script prints each run's
# time and the check's summary, and it exits with status 1 when a run fails or a digest differs.
# The platforms default to tcg and kvm.  The products lie in OUT, build/baremetal/a64-fpexhaust
# unless set.  A run of every chunk spends hours of the host's cores on Talos's digests: the
# commands stripes and join of a64-fpexhaust split that work over hosts.
# Usage: tests/baremetal/a64-fpexhaust.sh SAMPLE [PLATFORM...]
set -euo pipefail
[ "$#" -ge 1 ] || { echo "usage: tests/baremetal/a64-fpexhaust.sh SAMPLE [PLATFORM...]" >&2
  exit 2; }
sample=$1
shift
[ "$#" -gt 0 ] || set -- tcg kvm
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-fpexhaust}")
qemu=${QEMU:-qemu-system-aarch64}
tasks=${TASKS:-4}
for p in "$@"; do
  case "$p" in
    tcg | kvm | kvm:[0-9]*) ;;
    *) echo "a platform is tcg, kvm, or kvm:N, not $p" >&2; exit 2 ;;
  esac
done
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 30m lake --log-level error build a64-fpexhaust
x=.lake/build/bin/a64-fpexhaust
tools/leanrun --timeout 10m lake env $x gen "$out" "$sample" ${CASES:-all}
tools/leanrun --timeout 600m --cpus "$tasks" lake env $x expect "$out" "$tasks"
status=0
if [ "$sample" != 0 ]; then
  tools/leanrun --timeout 600m --cpus "$tasks" lake env $x expect "$out" "$tasks" model
  if cmp -s "$out/ex.expect" "$out/ex.model"; then
    echo "pass: the model's digests equal Talos's"
  else
    echo "fail: the model's digests differ from Talos's"
    status=1
  fi
fi
for accel in tcg kvm; do
  if printf '%s\n' "$@" | grep -q "^$accel"; then
    ACCEL=$accel tests/baremetal/a64-loadcheck.sh "$out/ex.img" || status=1
  fi
done
for p in "$@"; do
  case "$p" in
    tcg) opts=(-cpu cortex-a57); pin=() ;;
    kvm) opts=(-accel kvm -cpu host); pin=() ;;
    *) opts=(-accel kvm -cpu host); pin=(taskset -c "${p#kvm:}") ;;
  esac
  name=${p/:/-}
  (
    start=$(date +%s%N)
    qcode=0
    "${pin[@]}" timeout "${TIMEOUT:-7200}" "$qemu" -M virt "${opts[@]}" -m 1G -display none \
      -monitor none -serial "file:$out/$name.serial" -kernel "$out/ex.img" </dev/null || qcode=$?
    ms=$((($(date +%s%N) - start) / 1000000))
    printf '%s %d.%03d\n' "$qcode" $((ms / 1000)) $((ms % 1000)) >"$out/$name.run"
    if [ "$qcode" -eq 0 ]; then
      ccode=0
      tools/leanrun --timeout 60m lake env $x check "$out" "$out/$name.serial" \
        >"$out/$name.check" 2>&1 || ccode=$?
      echo "$ccode" >"$out/$name.checked"
    fi
  ) &
done
wait
for p in "$@"; do
  name=${p/:/-}
  read -r qcode secs <"$out/$name.run"
  if [ "$qcode" -ne 0 ]; then
    echo "fail: $p: QEMU exited with status $qcode after $secs s"
    status=1
  elif [ "$(cat "$out/$name.checked")" = 0 ]; then
    echo "pass: $p: $secs s, $(tail -n 1 "$out/$name.check")"
  else
    echo "fail: $p: $secs s"
    grep -m 20 -e '^differ' -e '^fail' "$out/$name.check" || :
    tail -n 1 "$out/$name.check"
    status=1
  fi
done
exit "$status"
