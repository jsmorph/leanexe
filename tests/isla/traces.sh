#!/usr/bin/env bash
# The Isla traces that LeanExe/A64/Isla/Check.lean reads: ADD X3, X4, X5 (8b050083), SUBS X3, X4,
# X5 (eb050083), and LDR X3, [X4, #24] (f9400c83), from the Armv9.4-A snapshot of the Sail model
# (isla-snapshots d8b31014, armv9p4.ir) with Isla e9b5d945 and Z3 4.12.6, as built in
# ~/isla-probe on edgexpert-18ff.  The entry point isla_footprint_no_init skips the reset, so the
# configuration's registers appear as assume-reg events and every register that the configuration
# leaves unset is a fresh variable.  The processor runs at EL1 with SP_EL1, with debug exceptions
# masked and the debug registers of Islaris's configuration, and SCTLR_EL1 is 0x04000208: the MMU,
# the alignment check, and big-endian data are off, and SA, the stack pointer's alignment check,
# is on.  -L AddWithCarry removes the forks on the flags whose outcomes agree.  The load's
# address, X4 + 24, is a multiple of 8 in 0x40000000-0x7FFFFFFF, which excludes the devices of the
# Sail model at 0x2C000000 and 0x3C000000.  The traces go to DIR, ~/isla-probe/check unless set.
# Usage: tests/isla/traces.sh [DIR]
set -euo pipefail
dir=${1:-$HOME/isla-probe/check}
cd "$HOME/isla-probe"
export LD_LIBRARY_PATH=$HOME/isla-probe/z3/install/lib
run() {
  local name=$1
  shift
  systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 timeout 600 \
    isla/target/release/isla-footprint -A ir/armv9p4.ir -C isla/configs/armv9p4.toml \
    -f isla_footprint_no_init -s --simplify-registers --tree \
    -R PSTATE.EL=0b01 -R PSTATE.SP=0b1 -R PSTATE.D=0b1 \
    -R '_EDSCR={bits=0x00000002}' -R 'MDCCSR_EL0={bits=0x0000000000000000}' \
    -R 'OSLSR_EL1={bits=0x0000000000000000}' -R 'OSDLR_EL1={bits=0x0000000000000000}' \
    -R 'DBGPRCR_EL1={bits=0x0000000000000000}' -R 'SCTLR_EL1={bits=0x0000000004000208}' \
    "$@" > "$dir/$name.trace"
}
run add -L AddWithCarry -x -e big -i 8b050083
run subs -L AddWithCarry -x -e big -i eb050083
run ldr -x -e big -i f9400c83 \
  --reset-constraint '= (bvand (bvadd R4 0x0000000000000018) 0xffffffffc0000007) 0x0000000040000000'
