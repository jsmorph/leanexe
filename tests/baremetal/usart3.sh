#!/usr/bin/env bash
# The programs with requests for USART3 of the NUCLEO-F767ZI: the echo of usart3Tick
# (tests/TestSupport/Bare/Req.lean) and the energy controller of gwTickUsart3
# (Demos/Energy/Loop.lean).
#
# "usart3.sh build" builds them.  native-bare emit-usart3 writes each program's C text, the
# translation of its module followed by the main that runs the step forever and performs each
# request with a volatile 32-bit load or store of lx_reg, and the names of the functions that take
# the call depth.  The ARMv7-M tree's clightgen reads each C text back, and native-bare
# check-usart3 compares the whole program with the program of the theorem.  Given DIR, the script
# skips these steps and takes NAME.c and NAME.depth from DIR, as an earlier run wrote them.  Each
# program NAME is built with tools/baremetal/armv7m/build.sh for the board nucleo-f767zi, whose
# stack bound and access check must hold, and OBJCOPY writes NAME.bin, the image's loadable
# sections from 0x08000000, the start of the board's flash.
#
# "usart3.sh run NAME DEVICE" plays the far end of USART3 for the program NAME through the serial
# port DEVICE, the virtual COM port of the board's ST-LINK, after the user writes NAME.bin to the
# board's flash at 0x08000000 and resets the board.  For echo, tests/baremetal/uart_echo.py checks
# each reply.  For gateway, tests/baremetal/uart_gateway.py simulates TICKS minutes, 1,440 unless
# set, of the plant of the minute series SERIES, $HOME/data/energy/series/nist-2015.csv unless
# set, and checks the commands and the monitoring, and native-bare gateway-run then runs the
# gateway in native Lean on the same input records, whose output records must equal the board's.
#
# The products lie in OUT, build/baremetal/usart3 unless set: NAME.elf with the files of build.sh,
# NAME.bin, NAME.echo, the line that the host script prints, NAME.stderr, the messages of uv, and
# for gateway the records NAME.records.in, NAME.records.out, and NAME.records.lean.  CCOMP,
# CCOMP_STDLIB, and CLIGHTGEN name CompCert 3.18's driver, run-time library, and clightgen
# configured armv7m-eabihf, OBJCOPY, OBJDUMP, and NM name objcopy, objdump, and nm for ARM, UV
# names uv, and TIMEOUT, 120 unless set, bounds each wait of the host script in seconds.
# Usage: tests/baremetal/usart3.sh build [DIR]
#        tests/baremetal/usart3.sh run NAME DEVICE
set -euo pipefail
usage() {
  echo "usage: tests/baremetal/usart3.sh build [DIR] | run NAME DEVICE" >&2
  exit 2
}
[ "$#" -ge 1 ] || usage
root=$(cd "$(dirname "$0")/../.." && pwd)
here=$root/tests/baremetal
out=${OUT:-$root/build/baremetal/usart3}
uv=${UV:-uv}

case $1 in
  build)
    [ "$#" -le 2 ] || usage
    clightgen=${CLIGHTGEN:-clightgen}
    objcopy=${OBJCOPY:-arm-none-eabi-objcopy}
    dir=$out
    if [ "$#" -eq 2 ]; then
      dir=$(cd "$2" && pwd)
    fi
    rm -rf "$out"
    mkdir -p "$out"
    if [ "$#" -eq 1 ]; then
      cd "$root"
      tools/leanrun --timeout 60m lake --log-level error build native-bare
      tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare emit-usart3 "$out"
      for c in "$out"/*.c; do
        (cd "$out" && "$clightgen" "$(basename "$c")")
      done
      tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare check-usart3 "$out"
    fi
    status=0
    for c in "$dir"/*.c; do
      name=$(basename "${c%.c}")
      if BOARD=nucleo-f767zi STACK_DEPTHS=$dir/$name.depth "$root/tools/baremetal/armv7m/build.sh" \
          "$out/$name.elf" "$c" >"$out/$name.build" 2>&1 &&
          "$objcopy" -O binary "$out/$name.elf" "$out/$name.bin"; then
        echo "built: $name: $(wc -c <"$out/$name.bin") bytes of flash;" \
          "bound $(cut -d' ' -f1 "$out/$name.elf.bound")," \
          "helpers $(awk '{print $3}' "$out/$name.elf.helpers" | paste -sd' ')"
      else
        echo "fail: $name: $(paste -sd' ' "$out/$name.build" | head -c 400)"
        status=1
      fi
    done
    exit "$status"
    ;;
  run)
    [ "$#" -eq 3 ] || usage
    name=$2
    device=$3
    series=${SERIES:-$HOME/data/energy/series/nist-2015.csv}
    mkdir -p "$out"
    case $name in
      echo) host=(uart_echo.py) ;;
      gateway) host=(uart_gateway.py --ticks "${TICKS:-1440}" "$series" "$out/$name.records") ;;
      *) usage ;;
    esac
    if ! "$uv" run "$here/${host[0]}" --timeout "${TIMEOUT:-120}" --device "$device" \
        "${host[@]:1}" >"$out/$name.echo" 2>"$out/$name.stderr"; then
      echo "fail: $name: $(cat "$out/$name.echo" "$out/$name.stderr" | paste -sd' ' | head -c 400)"
      exit 1
    fi
    echo "pass: $name: $(cat "$out/$name.echo")"
    if [ "$name" = gateway ]; then
      (cd "$root" && tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare gateway-run \
        "$out/$name.records.in" "$out/$name.records.lean") >"$out/$name.native" 2>&1
      if ! cmp -s "$out/$name.records.out" "$out/$name.records.lean"; then
        echo "fail: $name: the output records differ from native Lean's:" \
          "$(cmp "$out/$name.records.out" "$out/$name.records.lean" 2>&1 | head -c 300)" \
          "$(head -c 300 "$out/$name.native")"
        exit 1
      fi
      echo "pass: $name: the output records equal native Lean's for" \
        "$(wc -l <"$out/$name.records.in") input records"
    fi
    ;;
  *)
    usage
    ;;
esac
