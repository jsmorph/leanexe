#!/usr/bin/env bash
# The programs with requests for USART3 of the NUCLEO-F767ZI, the echo of usart3Tick
# (tests/TestSupport/Bare/Req.lean) and the energy controller of gwTickUsart3
# (Demos/Energy/Loop.lean), and two images of the echo whose startup code faults before main.
#
# "usart3.sh build" builds them.  native-bare emit-usart3 writes each program's C text, the
# translation of its module followed by the main that runs the step forever and performs each
# request with a volatile 32-bit load or store of lx_reg, and the names of the functions that take
# the call depth.  The ARMv7-M tree's clightgen reads each C text back, and native-bare
# check-usart3 compares the whole program with the program of the theorem.  Given DIR, the script
# skips these steps and takes NAME.c and NAME.depth from DIR, as an earlier run wrote them.  DIR
# must lie outside OUT, which the build empties.  Each program NAME is built with
# tools/baremetal/armv7m/build.sh for the board nucleo-f767zi, whose stack bound and access check
# must hold, and OBJCOPY writes NAME.bin, the image's loadable sections from 0x08000000, the start
# of the board's flash.  The images guard and ldrd are the echo built with GUARD_TEST, a store to
# the word below the stack, and with UNALIGNED_LDRD_TEST, an LDRD from an odd address, without the
# stack bound and the access check, which rejects that LDRD.
#
# "usart3.sh run NAME DEVICE" plays the far end of USART3 for the image NAME through the serial
# port DEVICE, the virtual COM port of the board's ST-LINK, after the user writes NAME.bin to the
# board's flash at 0x08000000.  For echo, tests/baremetal/uart_echo.py checks each reply.  For
# gateway, tests/baremetal/uart_gateway.py simulates TICKS minutes, 1,440 unless set, of the plant
# of the minute series SERIES, $HOME/data/energy/series/nist-2015.csv unless set, and checks the
# commands and the monitoring, and native-bare gateway-run, which must succeed, then runs the
# gateway in native Lean on the same input records, whose output records must equal the board's.
# The user resets the board before the run of echo or gateway, and after the start of the run of
# guard or ldrd, for which tests/baremetal/uart_report.py reads the fault report.  As
# tests/baremetal/m7.sh requires on mps2-an500, the report of guard must show a MemManage fault,
# exception 4, with CFSR 0x00000082, DACCVIOL and MMARVALID, and MMFAR at the word below the
# stack, and that of ldrd a UsageFault, exception 6, with CFSR 0x01000000, UNALIGNED.
#
# "usart3.sh emulate NAME" runs NAME.elf in Renode on its model of the NUCLEO-F767ZI,
# platforms/boards/nucleo_f767zi.repl.  For echo and gateway, USART3 lies on a pseudo-terminal,
# NAME.pty, and a hook at main logs "reached main".  The model drops a byte that arrives while UE
# or RE is clear, so the script waits for that line, which follows board_init, before it plays the
# far end through the pseudo-terminal as "run" does.  For guard, Renode writes USART3's output to
# NAME.uart, and the script checks its first line as "run" does.  Renode's Cortex-M7 takes an
# unaligned LDRD without a fault, so ldrd runs only on a board.  Renode loads the
# image's segments, takes the vector table from 0x08000000, and models USART3's registers: it sends
# a byte only while UE and TE are set, takes one only while UE and RE are set, sets RXNE while its
# queue of received bytes is not empty, and always reports TXE set.  It models neither the RCC's
# clock enables, nor the connection of PD8 and PD9 to USART3, nor time at the board's clock, and
# its queue never overruns.  Renode's log, NAME.renode, may hold no warning or error other than
# those of its translation cache and of RCC_DCKCFGR2, at offset 0x90, which its RCC model lacks.
# On its first run Renode downloads the register descriptions that the platform names from
# dl.antmicro.com.
#
# The products lie in OUT, build/baremetal/usart3 unless set: NAME.elf with the files of build.sh,
# NAME.bin, NAME.echo, the line that the host script prints, NAME.stderr, the messages of uv, and
# for gateway the records NAME.records.in, NAME.records.out, and NAME.records.lean.  CCOMP,
# CCOMP_STDLIB, and CLIGHTGEN name CompCert 3.18's driver, run-time library, and clightgen
# configured armv7m-eabihf, OBJCOPY, OBJDUMP, and NM name objcopy, objdump, and nm for ARM, UV
# names uv, RENODE names Renode 1.17.0's renode, and TIMEOUT, 120 unless set, bounds each wait of
# the host script in seconds.
# Usage: tests/baremetal/usart3.sh build [DIR]
#        tests/baremetal/usart3.sh run NAME DEVICE
#        tests/baremetal/usart3.sh emulate NAME
set -euo pipefail
usage() {
  echo "usage: tests/baremetal/usart3.sh build [DIR] | run NAME DEVICE | emulate NAME" >&2
  exit 2
}
[ "$#" -ge 1 ] || usage
root=$(cd "$(dirname "$0")/../.." && pwd)
here=$root/tests/baremetal
out=$(realpath -m "${OUT:-$root/build/baremetal/usart3}")
uv=${UV:-uv}
timeout=${TIMEOUT:-120}
nm=${NM:-arm-none-eabi-nm}

# Prints the start of the report that the fault image $1 must give.
want_report() {
  local bottom
  case $1 in
    guard)
      bottom=$("$nm" "$out/guard.elf" | awk '$3 == "__stack_bottom" { print "0x" $1 }')
      printf 'R:fault 4 cfsr 0x00000082 hfsr 0x00000000 mmfar 0x%08x ' $((bottom - 4))
      ;;
    ldrd)
      printf 'R:fault 6 cfsr 0x01000000 '
      ;;
  esac
}

# Checks that the line $2 is the report that the fault image $1 must give.
check_report() {
  local want
  want=$(want_report "$1")
  if [ "${2#"$want"}" = "$2" ]; then
    echo "fail: $1: the report \"$2\" does not start with \"$want\""
    return 1
  fi
  echo "pass: $1: $2"
}

# Plays the far end of USART3 for the image $1 through the serial port $2 and, for the gateway,
# compares the output records with native Lean's.  Fails with a line that names the cause.
host_run() {
  local name=$1 device=$2 series=${SERIES:-$HOME/data/energy/series/nist-2015.csv} host
  case $name in
    echo) host=(uart_echo.py) ;;
    gateway)
      host=(uart_gateway.py --ticks "${TICKS:-1440}" "$series" "$out/$name.records")
      rm -f "${out:?}/$name.records.in" "${out:?}/$name.records.out" \
        "${out:?}/$name.records.lean"
      ;;
    guard|ldrd) host=(uart_report.py) ;;
    *) usage ;;
  esac
  if ! "$uv" run "$here/${host[0]}" --timeout "$timeout" --device "$device" \
      "${host[@]:1}" >"$out/$name.echo" 2>"$out/$name.stderr"; then
    echo "fail: $name: $(cat "$out/$name.echo" "$out/$name.stderr" | paste -sd' ' | head -c 400)"
    return 1
  fi
  case $name in
    guard|ldrd)
      check_report "$name" "$(cat "$out/$name.echo")"
      return
      ;;
  esac
  echo "pass: $name: $(cat "$out/$name.echo")"
  if [ "$name" = gateway ]; then
    if ! (cd "$root" && tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare \
        gateway-run "$out/$name.records.in" "$out/$name.records.lean") >"$out/$name.native" 2>&1
    then
      echo "fail: $name: native-bare gateway-run failed:" \
        "$(paste -sd' ' "$out/$name.native" | head -c 400)"
      return 1
    fi
    if ! cmp -s "$out/$name.records.out" "$out/$name.records.lean"; then
      echo "fail: $name: the output records differ from native Lean's:" \
        "$(cmp "$out/$name.records.out" "$out/$name.records.lean" 2>&1 | head -c 300)" \
        "$(head -c 300 "$out/$name.native")"
      return 1
    fi
    echo "pass: $name: the output records equal native Lean's for" \
      "$(wc -l <"$out/$name.records.in") input records"
  fi
}

case $1 in
  build)
    [ "$#" -le 2 ] || usage
    clightgen=${CLIGHTGEN:-clightgen}
    objcopy=${OBJCOPY:-arm-none-eabi-objcopy}
    dir=$out
    if [ "$#" -eq 2 ]; then
      dir=$(realpath "$2")
      case $dir/ in
        "$out"/*)
          echo "tests/baremetal/usart3.sh: DIR lies in OUT, $out, which the build empties" >&2
          exit 2
          ;;
      esac
    fi
    rm -rf "${out:?}"
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
    for image in guard:GUARD_TEST ldrd:UNALIGNED_LDRD_TEST; do
      name=${image%%:*}
      define=${image#*:}
      if BOARD=nucleo-f767zi "$root/tools/baremetal/armv7m/build.sh" "$out/$name.elf" \
          "$dir/echo.c" -- "-D$define" >"$out/$name.build" 2>&1 &&
          "$objcopy" -O binary "$out/$name.elf" "$out/$name.bin"; then
        echo "built: $name: the echo with $define, $(wc -c <"$out/$name.bin") bytes of flash"
      else
        echo "fail: $name: $(paste -sd' ' "$out/$name.build" | head -c 400)"
        status=1
      fi
    done
    exit "$status"
    ;;
  run)
    [ "$#" -eq 3 ] || usage
    case $2 in
      guard|ldrd) echo "usart3.sh: reset the board within $timeout s" >&2 ;;
    esac
    host_run "$2" "$3"
    ;;
  emulate)
    [ "$#" -eq 2 ] || usage
    name=$2
    renode=${RENODE:-renode}
    [ -f "$out/$name.elf" ] || { echo "fail: $name: $out/$name.elf is missing"; exit 1; }
    pty=$out/$name.pty
    uart=$out/$name.uart
    rm -f "${out:?}/$name.pty" "${out:?}/$name.uart" "${out:?}/$name.renode.pid"
    case $name in
      echo|gateway)
        main=$("$nm" "$out/$name.elf" | awk '$3 == "main" { print $1 }')
        setup="emulation CreateUartPtyTerminal \"usart3\" \"$pty\" true
connector Connect sysbus.usart3 usart3
sysbus LoadELF @$out/$name.elf
cpu AddHook $(printf '0x%x' $((0x$main & ~1))) \"self.InfoLog('reached main')\""
        ;;
      guard)
        setup="sysbus.usart3 CreateFileBackend @$uart true
sysbus LoadELF @$out/$name.elf"
        ;;
      ldrd)
        echo "tests/baremetal/usart3.sh: Renode takes an unaligned LDRD without a fault;" \
          "run ldrd on a board" >&2
        exit 2
        ;;
      *)
        usage
        ;;
    esac
    cat >"$out/$name.resc" <<EOF
mach create "nucleo-f767zi"
machine LoadPlatformDescription @platforms/boards/nucleo_f767zi.repl
$setup
start
EOF
    "$renode" --disable-gui --plain -P -1 --pid-file "$out/$name.renode.pid" "$out/$name.resc" \
      >"$out/$name.renode" 2>&1 &
    renode_job=$!
    # Waits until the command $1 succeeds or Renode exits, for at most TIMEOUT seconds, and
    # returns the command's last status.
    await() {
      for _ in $(seq "$timeout"); do
        eval "$1" && return
        kill -0 "$renode_job" 2>/dev/null || break
        sleep 1
      done
      eval "$1"
    }
    status=0
    case $name in
      echo|gateway)
        if ! await 'grep -aq "cpu: reached main" "$out/$name.renode"' || [ ! -e "$pty" ]; then
          echo "fail: $name: Renode did not reach main: $(tail -c 300 "$out/$name.renode")"
          status=1
        else
          host_run "$name" "$pty" || status=1
        fi
        ;;
      guard)
        if ! await '[ -f "$uart" ] && [ "$(wc -l <"$uart")" -ge 1 ]'; then
          echo "fail: $name: Renode wrote no line to $uart:" \
            "$(head -c 200 "$uart" 2>/dev/null) $(tail -c 300 "$out/$name.renode")"
          status=1
        else
          check_report "$name" "$(head -n 1 "$uart")" || status=1
        fi
        ;;
    esac
    kill "$(cat "$out/$name.renode.pid")" 2>/dev/null || :
    wait "$renode_job" 2>/dev/null || :
    unexpected=$(grep -a '\[WARNING\]\|\[ERROR\]' "$out/$name.renode" |
      grep -av 'Translation cache size [0-9]* is larger than maximum allowed' |
      grep -av 'rcc: Unhandled \(read from\|write to\) offset 0x90[.,]' | head -c 400 || :)
    if [ -n "$unexpected" ]; then
      echo "fail: $name: Renode logged $unexpected"
      status=1
    fi
    exit "$status"
    ;;
  *)
    usage
    ;;
esac
