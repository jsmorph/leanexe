#!/usr/bin/env bash
# The test of the floating-point forms' meanings in LeanExe/A64/Machine.lean against QEMU and the
# processor (tests/TestSupport/A64/FpVectors.lean).  It builds a64-fpvectors, writes the arm64
# Image of COUNT vectors of each of FADD, FSUB, FMUL, FDIV, FSQRT, UCVTF, FCMP, and FCVTZU from
# SEED, checks QEMU's loading of it with tests/baremetal/a64-loadcheck.sh under each accelerator
# that the platforms use, and runs it on QEMU's virt machine with 1 GiB of RAM on every PLATFORM at
# once: tcg, under which QEMU emulates a Cortex-A57, kvm, under KVM on the host's processor, or
# kvm:N, under KVM pinned with taskset to processor N.  Each run must end within TIMEOUT seconds,
# 3600 unless set, with QEMU's status 0, and after each run a64-fpvectors check compares every
# result word of its UART output with the model and writes each block's and each form's counts
# and every disagreement to OUT/PLATFORM.check, with a colon in PLATFORM written as a hyphen.
# The script prints each run's time and the check's summary, and it exits with status 1 when a
# run fails or a result differs.  The platforms default to tcg and kvm.  FORMS, when set, names the
# forms whose vectors the Image holds, such as fcvtzu, every form unless set.  The products lie in
# OUT, build/baremetal/a64-fpvectors unless set.
# Usage: tests/baremetal/a64-fpvectors.sh SEED COUNT [PLATFORM...]
set -euo pipefail
[ "$#" -ge 2 ] || { echo "usage: tests/baremetal/a64-fpvectors.sh SEED COUNT [PLATFORM...]" >&2
  exit 2; }
seed=$1
count=$2
shift 2
[ "$#" -gt 0 ] || set -- tcg kvm
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/baremetal/a64-fpvectors}")
qemu=${QEMU:-qemu-system-aarch64}
for p in "$@"; do
  case "$p" in
    tcg | kvm | kvm:[0-9]*) ;;
    *) echo "a platform is tcg, kvm, or kvm:N, not $p" >&2; exit 2 ;;
  esac
done
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 30m lake --log-level error build a64-fpvectors
tools/leanrun --timeout 60m lake env .lake/build/bin/a64-fpvectors gen "$seed" "$count" "$out" \
  ${FORMS:-}
status=0
for accel in tcg kvm; do
  if printf '%s\n' "$@" | grep -q "^$accel"; then
    ACCEL=$accel tests/baremetal/a64-loadcheck.sh "$out/fp.img" || status=1
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
    "${pin[@]}" timeout "${TIMEOUT:-3600}" "$qemu" -M virt "${opts[@]}" -m 1G -display none \
      -monitor none -serial "file:$out/$name.serial" -kernel "$out/fp.img" </dev/null || qcode=$?
    ms=$((($(date +%s%N) - start) / 1000000))
    printf '%s %d.%03d\n' "$qcode" $((ms / 1000)) $((ms % 1000)) >"$out/$name.run"
    if [ "$qcode" -eq 0 ]; then
      ccode=0
      tools/leanrun --timeout 60m lake env .lake/build/bin/a64-fpvectors check "$out" \
        "$out/$name.serial" >"$out/$name.check" 2>&1 || ccode=$?
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
