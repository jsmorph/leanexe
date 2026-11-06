#!/usr/bin/env bash
# The trace add.trace of ADD Xd, Xn, Xm with Rd, Rn, and Rm symbolic, in the startup's
# configuration of the Isla probe of 2026-11-06 (EL1 with SP_EL1, debug exceptions masked,
# SCTLR_EL1 0x30d0198d, TCR_EL1 0x80a03520, MAIR_EL1 0xff00, FEAT_GCS absent), with Isla
# e9b5d945, Z3 4.12.6, and armv9p4.ir of isla-snapshots d8b31014, as built in ~/isla-probe on
# edgexpert-18ff.  __isla_vector_gpr makes Isla read and write a general register at a symbolic
# index through read_register_from_vector and write_register_from_vector, and -L AddWithCarry
# removes the forks on the flags.  The trace goes to DIR, the current directory unless set.
# Usage: tests/isla/dev/add.sh [DIR]
set -euo pipefail
dir=$(realpath "${1:-.}")
cd "$HOME/isla-probe"
export LD_LIBRARY_PATH=$HOME/isla-probe/z3/install/lib
systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 timeout 600 \
  isla/target/release/isla-footprint -A ir/armv9p4.ir -C isla/configs/armv9p4.toml \
  -f isla_footprint_no_init -s --simplify-registers --tree -I FEAT_GCS_IMPLEMENTED=false \
  -R PSTATE.EL=0b01 -R PSTATE.SP=0b1 -R PSTATE.D=0b1 \
  -R '_EDSCR={bits=0x00000002}' -R 'MDCCSR_EL0={bits=0x0000000000000000}' \
  -R 'OSLSR_EL1={bits=0x0000000000000000}' -R 'OSDLR_EL1={bits=0x0000000000000000}' \
  -R 'DBGPRCR_EL1={bits=0x0000000000000000}' -R 'SCTLR_EL1={bits=0x0000000030d0198d}' \
  -R 'TCR_EL1={bits=0x0000000080a03520}' -R 'MAIR_EL1={bits=0x000000000000ff00}' \
  -I __isla_vector_gpr=true -L AddWithCarry \
  --partial -i '10001011000 Rm:5 000000 Rn:5 Rd:5' > "$dir/add.trace"
