#!/usr/bin/env bash
# The programs with requests through the Cortex-M7 back end on the NUCLEO-F767ZI: the echo of
# usart3Tick, NAME echo, and the energy controller's gateway of gwTickUsart3, NAME gateway.
#
# "m7-board.sh check NAME" builds m7-windows and the loop theorems of
# tests/TestSupport/M7/NucleoLoop.lean or GwLoop.lean, writes with m7-windows board or
# gateway-board the image that LeanExe/M7/Board.lean lays out, NAME.bin, with the addresses of main
# and of its loop's head in NAME.addr, and elaborates tests/TestSupport/M7/NucleoFile.lean or
# GwBoardFile.lean in the directory of the image under a memory cap of MEM, 12G for the echo and
# 16G for the gateway unless set, so that the kernel checks that the file holds the image's bytes,
# the gateway's in parts, and the theorems hold of the file.  It requires that each theorem whose
# axioms that file prints depends on no axiom beyond propext, Classical.choice, and Quot.sound,
# and reports the check's elapsed time and peak memory.  It also writes the measurement images of
# tests/TestSupport/M7/Dwt.lean, NAME-dwt.bin and for the echo div-dwt.bin, which no theorem
# covers.
#
# "m7-board.sh emulate NAME" runs NAME.bin in Renode on its model of the NUCLEO-F767ZI,
# platforms/boards/nucleo_f767zi.repl, as tests/baremetal/usart3.sh emulate runs the C path's
# images.  Renode's model maps the flash at 0x08000000 alone, so the script maps a memory of the
# flash's size at 0x00200000, the flash's ITCM address, loads the image at both addresses, and sets
# VTOR to 0x00200000, the address that the board's BOOT_ADD0 names.  USART3 lies on a
# pseudo-terminal, NAME.pty, and a hook at main logs "reached main", which follows the board's
# initialization; the script then plays the far end through the pseudo-terminal as "run" does.
# Renode's log, NAME.renode, may hold no warning or error other than those of its translation
# cache and of RCC_DCKCFGR2, at offset 0x90, which its RCC model lacks.
#
# "m7-board.sh run NAME DEVICE" writes NAME.bin to the board's flash at 0x08000000 with st-flash,
# reads the flash back and compares its first bytes with the file, since st-flash 1.8.0 reads a
# whole number of words, resets the board with st-flash, and plays the far end through the serial
# port DEVICE, the virtual COM port of the board's ST-LINK.  For the echo,
# tests/baremetal/uart_echo.py checks each reply, as tests/baremetal/usart3.sh run echo does.  For
# the gateway, tests/baremetal/uart_gateway.py simulates TICKS minutes, 1,440 unless set (5 under
# emulate), of the plant of the minute series SERIES, $HOME/data/energy/series/nist-2015.csv unless
# set, checks the commands and the monitoring, and writes the records NAME.records.in and
# NAME.records.out, and the script then reads USART_ISR over SWD into NAME.isr and requires ORE,
# bit 3, clear: the program never clears ORE, so no byte arrived while RXNE was set during the run.
# The reset over SWD leaves the debug state that the probe set, which the theorems' power-on
# premise excludes.  "m7-board.sh host NAME DEVICE" does what "run" does after the reset, without
# st-flash, for a run from the power-on reset of a replug after NAME.bin lies in the flash.
#
# "m7-board.sh measure-div" writes div-dwt.bin, the measurement image of udivmod64 and UDIV, to the
# board's flash as "run" does, waits 3 s after the reset, and reads the records and the boot log
# from DTCM over SWD into div.results and div.bootlog, which tests/baremetal/m7_dwt.py prints and
# checks.  "m7-board.sh measure NAME DEVICE" writes NAME-dwt.bin, the program with the cycles of
# each window, runs the host script through DEVICE as "run" does, with the gateway's records in
# NAME-dwt.records.in and NAME-dwt.records.out, and reads the window table and the boot log into
# NAME-dwt.results and NAME-dwt.bootlog, and for the gateway USART_ISR as "run" does.  st-flash
# attaches with --hot-plug for these reads, which halt the core.
#
# "m7-board.sh compare RECORDS" runs native-bare gateway-run on the input records RECORDS.in into
# RECORDS.lean and requires that they equal the output records RECORDS.out.  It needs Lean, and
# the board's runs need the board, so the two run where each is.
#
# The co-simulation of the model on the board (tests/TestSupport/M7/BoardCosim.lean) has three
# commands, the first and the last with Lean and the second with the board.  "m7-board.sh
# cosim-image SEED PER_FORM [seeded]" builds m7-cosim under a memory cap of MEM, 8G unless set,
# and writes cosim.bin, the image of PER_FORM cases of each form from the seed SEED followed by the
# fixed cases, without them when "seeded" is given, with its layout and the address and length of
# the results in cosim.layout.  DTCM holds the results of 963 cases, so PER_FORM is at most 22 with
# the fixed cases and 23 without them.  "m7-board.sh cosim" writes cosim.bin to the
# board as "run" does, waits 3 s after the reset, reads the results from DTCM over SWD into
# cosim.results, and requires the header's word 0x600DCAFE and as many saved cases as the image
# holds.  "m7-board.sh cosim-check SEED PER_FORM [seeded]", with the arguments of cosim-image,
# checks every case of cosim.results against the
# model with m7-cosim board-check, into cosim.check, and requires that all agree.  It then checks
# them against the model with ADC's carry in replaced by 0, into cosim.mutant, and requires that
# check to fail with at least one differing ADC case.
#
# The products lie in OUT, build/baremetal/m7-board unless set: the images, NAME.addr, the check's
# output and times, st-flash's messages in IMAGE.flash, and for emulate and run the host script's
# line NAME.echo and the messages of uv in NAME.stderr.  RENODE names Renode 1.17.0's renode,
# STFLASH names st-flash, UV names uv, and TIMEOUT, 120 unless set, bounds each wait of the host
# script in seconds.
# Usage: tests/baremetal/m7-board.sh check NAME | emulate NAME | run NAME DEVICE |
#          host NAME DEVICE | measure-div | measure NAME DEVICE | compare RECORDS |
#          cosim-image SEED PER_FORM [seeded] | cosim | cosim-check SEED PER_FORM [seeded]
set -euo pipefail
usage() {
  echo "usage: tests/baremetal/m7-board.sh check NAME | emulate NAME | run NAME DEVICE |" \
    "host NAME DEVICE | measure-div | measure NAME DEVICE | compare RECORDS |" \
    "cosim-image SEED PER_FORM [seeded] | cosim | cosim-check SEED PER_FORM [seeded]" >&2
  exit 2
}
[ "$#" -ge 1 ] || usage
root=$(cd "$(dirname "$0")/../.." && pwd)
here=$root/tests/baremetal
out=$(realpath -m "${OUT:-$root/build/baremetal/m7-board}")
uv=${UV:-uv}
stflash=${STFLASH:-st-flash}
timeout=${TIMEOUT:-120}
series=${SERIES:-$HOME/data/energy/series/nist-2015.csv}

# Requires that $1 names a program.
program() {
  case $1 in
    echo|gateway) ;;
    *) usage ;;
  esac
}

# The time of day, for the logs of the st-flash sessions.
stamp() {
  date '+%H:%M:%S'
}

# Writes the image $1 of OUT to the board's flash, reads the flash back and compares its first
# bytes with the file, and resets the board.  The log IMAGE.flash records each session's start.
flash() {
  local image=$out/$1 size
  [ -f "$image" ] || { echo "fail: $1 is missing"; return 1; }
  size=$(stat -c %s "$image")
  echo "$(stamp) st-flash write" >"$image.flash"
  "$stflash" write "$image" 0x08000000 >>"$image.flash" 2>&1 || {
    echo "fail: st-flash write $1: $(tail -c 300 "$image.flash")"; return 1; }
  echo "$(stamp) st-flash read" >>"$image.flash"
  "$stflash" read "$image.readback" 0x08000000 "$size" >>"$image.flash" 2>&1 || {
    echo "fail: st-flash read: $(tail -c 300 "$image.flash")"; return 1; }
  if ! cmp -s -n "$size" "$image" "$image.readback"; then
    echo "fail: the flash differs from $1: $(cmp -n "$size" "$image" "$image.readback")"
    return 1
  fi
  echo "pass: the flash holds the $size bytes of $1"
  echo "$(stamp) st-flash reset" >>"$image.flash"
  "$stflash" reset >>"$image.flash" 2>&1 || {
    echo "fail: st-flash reset: $(tail -c 300 "$image.flash")"; return 1; }
}

# Reads $3 bytes of the board's memory from $2 into $1 of OUT without a reset.  The log $1.read
# records the session's start.
readmem() {
  echo "$(stamp) st-flash --hot-plug read" >"$out/$1.read"
  "$stflash" --hot-plug read "$out/$1" "$2" "$3" >>"$out/$1.read" 2>&1 || {
    echo "fail: st-flash read $1: $(tail -c 300 "$out/$1.read")"; return 1; }
}

# Reads USART_ISR into $1.isr of OUT and requires ORE, bit 3, clear.
overrun() {
  local isr
  readmem "$1.isr" 0x4000481C 4 || return 1
  isr=$(od -An -tx4 -N4 "$out/$1.isr" | tr -d ' ')
  if (( (0x$isr >> 3) & 1 )); then
    echo "fail: $1: USART_ISR 0x$isr has ORE set"
    return 1
  fi
  echo "pass: $1: USART_ISR 0x$isr has ORE clear"
}

# Plays the far end of USART3 for program $1 through the serial port $2, with the gateway's
# records and the host script's line under the name $3 and the gateway's ticks $4.
host_run() {
  local host
  case $1 in
    echo) host=(uart_echo.py) ;;
    gateway)
      host=(uart_gateway.py --ticks "$4" "$series" "$out/$3.records")
      rm -f "${out:?}/$3.records.in" "${out:?}/$3.records.out"
      ;;
  esac
  if ! "$uv" run "$here/${host[0]}" --timeout "$timeout" --device "$2" "${host[@]:1}" \
      >"$out/$3.echo" 2>"$out/$3.stderr"; then
    echo "fail: $3: $(cat "$out/$3.echo" "$out/$3.stderr" | paste -sd' ' | head -c 400)"
    return 1
  fi
  echo "pass: $3: $(cat "$out/$3.echo")"
}

case $1 in
  check)
    [ "$#" -eq 2 ] || usage
    program "$2"
    name=$2
    cd "$root"
    mkdir -p "$out"
    case $name in
      echo) lib=TestSupport.M7.NucleoLoop cmd=board dwt=board-dwt file=NucleoFile count=12
        mem=${MEM:-12G} ;;
      gateway) lib=TestSupport.M7.GwLoop cmd=gateway-board dwt=gateway-dwt file=GwBoardFile
        count=13 mem=${MEM:-16G} ;;
    esac
    rm -f "${out:?}/$name".* "${out:?}/$name"-dwt.* "${out:?}/$file".*
    tools/leanrun --timeout 60m --memory-high "$mem" lake --log-level error build m7-windows \
      "$lib"
    tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows "$cmd" "$out/$name.bin" |
      tee "$out/$name.addr"
    tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows "$dwt" "$out/$name-dwt.bin"
    if [ "$name" = echo ]; then
      tools/leanrun --timeout 10m lake env .lake/build/bin/m7-windows div-dwt "$out/div-dwt.bin"
    fi
    status=0
    if /usr/bin/time -v tools/leanrun --timeout 30m --memory-high "$mem" lake env \
        sh -c 'cd "$1" && lean "$2"' sh "$out" "$root/tests/TestSupport/M7/$file.lean" \
        >"$out/$file.check" 2>"$out/$file.time"; then
      printed=$(grep -c 'axioms' "$out/$file.check" || true)
      other=$(grep 'depends on axioms' "$out/$file.check" | sed 's/.*\[\(.*\)\]$/\1/' |
        tr ',' '\n' | tr -d ' ' | grep -cvx 'propext\|Classical.choice\|Quot.sound' || true)
      if [ "$printed" = "$count" ] && [ "$other" = 0 ]; then
        echo "pass: the kernel's check of $name.bin, $(stat -c %s "$out/$name.bin") bytes," \
          "and the theorems over it"
      else
        echo "fail: the axioms of the check: $(head -c 600 "$out/$file.check")"
        status=1
      fi
    else
      echo "fail: the kernel's check of $name.bin: $(head -c 600 "$out/$file.check")"
      status=1
    fi
    grep -E "Elapsed \(wall|Maximum resident" "$out/$file.time"
    exit "$status"
    ;;
  emulate)
    [ "$#" -eq 2 ] || usage
    program "$2"
    name=$2
    renode=${RENODE:-renode}
    [ -f "$out/$name.bin" ] || { echo "fail: $name: $out/$name.bin is missing"; exit 1; }
    main=$(sed -n 's/.* main \(0x[0-9a-f]*\),.*/\1/p' "$out/$name.addr")
    [ -n "$main" ] || { echo "fail: $name: no address of main in $out/$name.addr"; exit 1; }
    pty=$out/$name.pty
    rm -f "${out:?}/$name.pty" "${out:?}/$name.renode.pid"
    cat >"$out/itcm.repl" <<EOF
flashItcm: Memory.MappedMemory @ sysbus 0x00200000
    size: 0x200000
EOF
    cat >"$out/$name.resc" <<EOF
mach create "nucleo-f767zi"
machine LoadPlatformDescription @platforms/boards/nucleo_f767zi.repl
machine LoadPlatformDescription @$out/itcm.repl
emulation CreateUartPtyTerminal "usart3" "$pty" true
connector Connect sysbus.usart3 usart3
sysbus LoadBinary @$out/$name.bin 0x08000000
sysbus LoadBinary @$out/$name.bin 0x00200000
cpu VectorTableOffset 0x00200000
cpu AddHook $main "self.InfoLog('reached main')"
start
EOF
    "$renode" --disable-gui --plain -P -1 --pid-file "$out/$name.renode.pid" "$out/$name.resc" \
      >"$out/$name.renode" 2>&1 &
    renode_job=$!
    status=0
    found=0
    for _ in $(seq "$timeout"); do
      if grep -aq "cpu: reached main" "$out/$name.renode" && [ -e "$pty" ]; then
        found=1
        break
      fi
      kill -0 "$renode_job" 2>/dev/null || break
      sleep 1
    done
    if [ "$found" = 1 ]; then
      host_run "$name" "$pty" "$name" "${TICKS:-5}" || status=1
    else
      echo "fail: $name: Renode did not reach main: $(tail -c 300 "$out/$name.renode")"
      status=1
    fi
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
  run|host)
    [ "$#" -eq 3 ] || usage
    program "$2"
    if [ "$1" = run ]; then
      flash "$2.bin"
    fi
    host_run "$2" "$3" "$2" "${TICKS:-1440}"
    if [ "$2" = gateway ]; then
      overrun "$2"
    fi
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
  measure)
    [ "$#" -eq 3 ] || usage
    program "$2"
    name=$2
    flash "$name-dwt.bin"
    status=0
    host_run "$name" "$3" "$name-dwt" "${TICKS:-1440}" || status=1
    case $name in
      echo) table=528 ;;
      gateway) table=2064 ;;
    esac
    readmem "$name-dwt.results" 0x20000000 "$table"
    readmem "$name-dwt.bootlog" 0x2001E000 264
    if [ "$name" = gateway ]; then
      overrun "$name-dwt" || status=1
    fi
    "$uv" run "$here/m7_dwt.py" bootlog "$out/$name-dwt.bootlog"
    "$uv" run "$here/m7_dwt.py" "$name" "$out/$name-dwt.results" || status=1
    exit "$status"
    ;;
  compare)
    [ "$#" -eq 2 ] || usage
    records=$(realpath -m "$2")
    cd "$root"
    if ! tools/leanrun --timeout 30m lake env .lake/build/bin/native-bare gateway-run \
        "$records.in" "$records.lean" >"$records.native" 2>&1; then
      echo "fail: native-bare gateway-run: $(paste -sd' ' "$records.native" | head -c 400)"
      exit 1
    fi
    if ! cmp -s "$records.out" "$records.lean"; then
      echo "fail: the output records differ from native Lean's:" \
        "$(cmp "$records.out" "$records.lean" 2>&1 | head -c 300)"
      exit 1
    fi
    echo "pass: the output records equal native Lean's for $(wc -l <"$records.in") input records"
    ;;
  cosim-image)
    [ "$#" -eq 3 ] || { [ "$#" -eq 4 ] && [ "$4" = seeded ]; } || usage
    cd "$root"
    mkdir -p "$out"
    rm -f "${out:?}"/cosim.*
    mem=${MEM:-8G}
    tools/leanrun --timeout 60m --memory-high "$mem" lake --log-level error build m7-cosim
    tools/leanrun --timeout 10m --memory-high "$mem" lake env .lake/build/bin/m7-cosim board \
      "$2" "$3" "$out/cosim.bin" "${@:4}" | tee "$out/cosim.layout"
    ;;
  cosim)
    [ "$#" -eq 1 ] || usage
    [ -f "$out/cosim.layout" ] || { echo "fail: cosim.layout is missing"; exit 1; }
    results=$(sed -n 's/^results \(0x[0-9a-f]*\) \([0-9]*\)$/\1 \2/p' "$out/cosim.layout")
    [ -n "$results" ] || { echo "fail: no results line in cosim.layout"; exit 1; }
    flash cosim.bin
    sleep 3
    readmem cosim.results "${results% *}" "${results#* }"
    read -r magic saved _ count _ < <(od -An -tx4 -j 64 -N 16 "$out/cosim.results")
    if [ "$magic" != 600dcafe ] || [ "$saved" != "$count" ]; then
      echo "fail: the board saved $((0x$saved)) of $((0x$count)) cases, header word 0x$magic"
      exit 1
    fi
    echo "pass: the board ran the $((0x$count)) cases and saved their results," \
      "${results#* } bytes from ${results% *}"
    ;;
  cosim-check)
    [ "$#" -eq 3 ] || { [ "$#" -eq 4 ] && [ "$4" = seeded ]; } || usage
    cd "$root"
    status=0
    if tools/leanrun --timeout 10m --memory-high "${MEM:-8G}" lake env .lake/build/bin/m7-cosim \
        board-check "$2" "$3" "$out/cosim.results" "${@:4}" >"$out/cosim.check" 2>&1; then
      echo "pass: $(tail -n 1 "$out/cosim.check")"
    else
      echo "fail: $(head -c 1200 "$out/cosim.check")"
      status=1
    fi
    if tools/leanrun --timeout 10m --memory-high "${MEM:-8G}" lake env .lake/build/bin/m7-cosim \
        board-check "$2" "$3" "$out/cosim.results" "${@:4}" adc-carry >"$out/cosim.mutant" 2>&1
    then
      echo "fail: the check with ADC's carry in replaced by 0 found no difference"
      status=1
    elif grep -q '^m7-cosim: differing cases by form: .*adcReg [1-9]' "$out/cosim.mutant"; then
      echo "pass: the mutated model is caught: $(grep '^m7-cosim: differing' "$out/cosim.mutant")"
    else
      echo "fail: the check with the mutated model: $(head -c 600 "$out/cosim.mutant")"
      status=1
    fi
    exit "$status"
    ;;
  *)
    usage
    ;;
esac
