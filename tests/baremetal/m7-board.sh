#!/usr/bin/env bash
# The echo of usart3Tick through the Cortex-M7 back end on the NUCLEO-F767ZI.
#
# "m7-board.sh check" builds m7-windows and the loop theorem of
# tests/TestSupport/M7/NucleoLoop.lean, writes with m7-windows board the image that
# LeanExe/M7/Board.lean lays out, echo.bin, with the addresses of main and of its loop's head in
# echo.addr, and elaborates tests/TestSupport/M7/NucleoFile.lean in the directory of the image
# under a memory cap of MEM, 12G unless set, so that the kernel checks that the file holds the
# image's bytes and the theorems hold of the file.  It requires that each theorem whose axioms
# that file prints depends on no axiom beyond propext, Classical.choice, and Quot.sound, and
# reports the check's elapsed time and peak memory.  It also writes the measurement images of
# tests/TestSupport/M7/Dwt.lean, echo-dwt.bin and div-dwt.bin, which no theorem covers.
#
# "m7-board.sh emulate" runs echo.bin in Renode on its model of the NUCLEO-F767ZI,
# platforms/boards/nucleo_f767zi.repl, as tests/baremetal/usart3.sh emulate runs the C path's
# images.  Renode's model maps the flash at 0x08000000 alone, so the script maps a memory of the
# flash's size at 0x00200000, the flash's ITCM address, loads the image at both addresses, and sets
# VTOR to 0x00200000, the address that the board's BOOT_ADD0 names.  USART3 lies on a
# pseudo-terminal, echo.pty, and a hook at main logs "reached main", which follows the board's
# initialization; the script then plays the far end through the pseudo-terminal with
# tests/baremetal/uart_echo.py.  Renode's log, echo.renode, may hold no warning or error other
# than those of its translation cache and of RCC_DCKCFGR2, at offset 0x90, which its RCC model
# lacks.
#
# "m7-board.sh run DEVICE" writes echo.bin to the board's flash at 0x08000000 with st-flash, reads
# the flash back and compares its first bytes with the file, since st-flash 1.8.0 reads a whole
# number of words, resets the board with st-flash, and plays the far end through the serial port
# DEVICE, the virtual COM port of the board's ST-LINK, with uart_echo.py, as
# tests/baremetal/usart3.sh run echo does.  The reset over SWD leaves the debug state that the
# probe set, which the theorem's power-on premise excludes.
#
# "m7-board.sh measure-div" writes div-dwt.bin, the measurement image of udivmod64 and UDIV, to the
# board's flash as "run" does, waits 3 s after the reset, and reads the records and the boot log
# from DTCM over SWD into div.results and div.bootlog, which tests/baremetal/m7_dwt.py prints and
# checks.  "m7-board.sh measure-echo DEVICE" writes echo-dwt.bin, the echo with the cycles of each
# window, runs uart_echo.py through DEVICE as "run" does, and reads the window table and the boot
# log into echo.results and echo.bootlog.  st-flash attaches with --hot-plug for these reads,
# which halt the core.
#
# The products lie in OUT, build/baremetal/m7-board unless set: the images, echo.addr, the check's
# output and times, st-flash's messages in IMAGE.flash, and for emulate and run the host script's
# line echo.echo and the messages of uv in echo.stderr.  RENODE names Renode 1.17.0's renode,
# STFLASH names st-flash, UV names uv, and TIMEOUT, 120 unless set, bounds each wait of the host
# script in seconds.
# Usage: tests/baremetal/m7-board.sh check | emulate | run DEVICE | measure-div |
#          measure-echo DEVICE
set -euo pipefail
usage() {
  echo "usage: tests/baremetal/m7-board.sh check | emulate | run DEVICE | measure-div |" \
    "measure-echo DEVICE" >&2
  exit 2
}
[ "$#" -ge 1 ] || usage
root=$(cd "$(dirname "$0")/../.." && pwd)
here=$root/tests/baremetal
out=$(realpath -m "${OUT:-$root/build/baremetal/m7-board}")
uv=${UV:-uv}
stflash=${STFLASH:-st-flash}
timeout=${TIMEOUT:-120}

# Writes the image $1 of OUT to the board's flash, reads the flash back and compares its first
# bytes with the file, and resets the board.
flash() {
  local image=$out/$1 size
  [ -f "$image" ] || { echo "fail: $1 is missing"; return 1; }
  size=$(stat -c %s "$image")
  "$stflash" write "$image" 0x08000000 >"$image.flash" 2>&1 || {
    echo "fail: st-flash write $1: $(tail -c 300 "$image.flash")"; return 1; }
  "$stflash" read "$image.readback" 0x08000000 "$size" >>"$image.flash" 2>&1 || {
    echo "fail: st-flash read: $(tail -c 300 "$image.flash")"; return 1; }
  if ! cmp -s -n "$size" "$image" "$image.readback"; then
    echo "fail: the flash differs from $1: $(cmp -n "$size" "$image" "$image.readback")"
    return 1
  fi
  echo "pass: the flash holds the $size bytes of $1"
  "$stflash" reset >>"$image.flash" 2>&1 || {
    echo "fail: st-flash reset: $(tail -c 300 "$image.flash")"; return 1; }
}

# Reads $3 bytes of the board's memory from $2 into $1 of OUT without a reset.
readmem() {
  "$stflash" --hot-plug read "$out/$1" "$2" "$3" >"$out/$1.read" 2>&1 || {
    echo "fail: st-flash read $1: $(tail -c 300 "$out/$1.read")"; return 1; }
}

# Plays the far end of USART3 through the serial port $1.
host_run() {
  if ! "$uv" run "$here/uart_echo.py" --timeout "$timeout" --device "$1" \
      >"$out/echo.echo" 2>"$out/echo.stderr"; then
    echo "fail: echo: $(cat "$out/echo.echo" "$out/echo.stderr" | paste -sd' ' | head -c 400)"
    return 1
  fi
  echo "pass: echo: $(cat "$out/echo.echo")"
}

case $1 in
  check)
    [ "$#" -eq 1 ] || usage
    cd "$root"
    rm -rf "${out:?}"
    mkdir -p "$out"
    tools/leanrun --timeout 60m lake --log-level error build m7-windows TestSupport.M7.NucleoLoop
    tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows board "$out/echo.bin" |
      tee "$out/echo.addr"
    tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows board-dwt "$out/echo-dwt.bin"
    tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows div-dwt "$out/div-dwt.bin"
    status=0
    if /usr/bin/time -v tools/leanrun --timeout 30m --memory-high "${MEM:-12G}" lake env \
        sh -c 'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/M7/NucleoFile.lean" \
        >"$out/board.check" 2>"$out/board.time"; then
      printed=$(grep -c 'axioms' "$out/board.check" || true)
      other=$(grep 'depends on axioms' "$out/board.check" | sed 's/.*\[\(.*\)\]$/\1/' |
        tr ',' '\n' | tr -d ' ' | grep -cvx 'propext\|Classical.choice\|Quot.sound' || true)
      if [ "$printed" = 12 ] && [ "$other" = 0 ]; then
        echo "pass: the kernel's check of echo.bin, $(stat -c %s "$out/echo.bin") bytes," \
          "and the theorems over it"
      else
        echo "fail: the axioms of the check: $(head -c 600 "$out/board.check")"
        status=1
      fi
    else
      echo "fail: the kernel's check of echo.bin: $(head -c 600 "$out/board.check")"
      status=1
    fi
    grep -E "Elapsed \(wall|Maximum resident" "$out/board.time"
    exit "$status"
    ;;
  emulate)
    [ "$#" -eq 1 ] || usage
    renode=${RENODE:-renode}
    [ -f "$out/echo.bin" ] || { echo "fail: echo: $out/echo.bin is missing"; exit 1; }
    main=$(sed -n 's/.* main \(0x[0-9a-f]*\),.*/\1/p' "$out/echo.addr")
    [ -n "$main" ] || { echo "fail: echo: no address of main in $out/echo.addr"; exit 1; }
    pty=$out/echo.pty
    rm -f "${out:?}/echo.pty" "${out:?}/echo.renode.pid"
    cat >"$out/itcm.repl" <<EOF
flashItcm: Memory.MappedMemory @ sysbus 0x00200000
    size: 0x200000
EOF
    cat >"$out/echo.resc" <<EOF
mach create "nucleo-f767zi"
machine LoadPlatformDescription @platforms/boards/nucleo_f767zi.repl
machine LoadPlatformDescription @$out/itcm.repl
emulation CreateUartPtyTerminal "usart3" "$pty" true
connector Connect sysbus.usart3 usart3
sysbus LoadBinary @$out/echo.bin 0x08000000
sysbus LoadBinary @$out/echo.bin 0x00200000
cpu VectorTableOffset 0x00200000
cpu AddHook $main "self.InfoLog('reached main')"
start
EOF
    "$renode" --disable-gui --plain -P -1 --pid-file "$out/echo.renode.pid" "$out/echo.resc" \
      >"$out/echo.renode" 2>&1 &
    renode_job=$!
    status=0
    found=0
    for _ in $(seq "$timeout"); do
      if grep -aq "cpu: reached main" "$out/echo.renode" && [ -e "$pty" ]; then
        found=1
        break
      fi
      kill -0 "$renode_job" 2>/dev/null || break
      sleep 1
    done
    if [ "$found" = 1 ]; then
      host_run "$pty" || status=1
    else
      echo "fail: echo: Renode did not reach main: $(tail -c 300 "$out/echo.renode")"
      status=1
    fi
    kill "$(cat "$out/echo.renode.pid")" 2>/dev/null || :
    wait "$renode_job" 2>/dev/null || :
    unexpected=$(grep -a '\[WARNING\]\|\[ERROR\]' "$out/echo.renode" |
      grep -av 'Translation cache size [0-9]* is larger than maximum allowed' |
      grep -av 'rcc: Unhandled \(read from\|write to\) offset 0x90[.,]' | head -c 400 || :)
    if [ -n "$unexpected" ]; then
      echo "fail: echo: Renode logged $unexpected"
      status=1
    fi
    exit "$status"
    ;;
  run)
    [ "$#" -eq 2 ] || usage
    flash echo.bin
    host_run "$2"
    ;;
  measure-div)
    [ "$#" -eq 1 ] || usage
    flash div-dwt.bin
    sleep 3
    readmem div.results 0x20000000 8192
    readmem div.bootlog 0x2001E000 264
    "$uv" run "$here/m7_dwt.py" bootlog "$out/div.bootlog"
    "$uv" run "$here/m7_dwt.py" div "$out/div.results"
    ;;
  measure-echo)
    [ "$#" -eq 2 ] || usage
    flash echo-dwt.bin
    host_run "$2"
    readmem echo.results 0x20000000 528
    readmem echo.bootlog 0x2001E000 264
    "$uv" run "$here/m7_dwt.py" bootlog "$out/echo.bootlog"
    "$uv" run "$here/m7_dwt.py" echo "$out/echo.results"
    ;;
  *)
    usage
    ;;
esac
