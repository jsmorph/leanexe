#!/usr/bin/env bash
# The Isla trace of SVC #0 at EL0, the system call of the A64 back end's Linux executables
# (LeanExe/A64/Linux.lean), in one of two profiles of a Linux kernel on edgexpert-18ff: el1, a
# kernel at EL1 under KVM, with the HCR_EL2 of the profile kvm of tests/isla/traces.sh, whose TGE
# is clear, and vhe, the host's kernel at EL2 with FEAT_VHE, whose HCR_EL2 is Linux 7.0's
# HCR_HOST_VHE_FLAGS (arch/arm64/include/asm/kvm_arm.h line 106): RW, TGE, E2H, AMO, IMO, and FMO.
# The trace comes from the Sail model, Isla, and Z3 of tests/isla/traces.sh, on
# armv9p4-checked.ir, with that script's settings of the debug registers, SCR_EL3, MDCR_EL2,
# VTCR_EL2, and the features of the profile kvm.  The processor runs at EL0 with SP_EL0
# (PSTATE.EL 0b00, PSTATE.SP 0b0), the state in which Linux runs a process (PSR_MODE_EL0t,
# arch/arm64/include/asm/processor.h line 339).  The other fields of PSTATE, the system control
# and translation registers of the kernel's level, SCTLR_ELx and TCR_ELx, and its vector base
# VBAR_ELx are symbolic, so the trace covers every value that the kernel may give them.  The
# opcode is the word 0xD4000001 of SVC #0, with no symbolic field.
#
# The traces are the starting point of a check that is not done.  CPACR_EL1, CPTR_EL3, SCR_EL3,
# MDSCR_EL1, MDCR_EL2, HFGITR_EL2, ZCR_EL2, and HCR_EL2 hold here Isla's defaults or the profile
# kvm's values, which Linux and its firmware do not hold, so a theorem over these traces would
# cover no state of a Linux process.  With Linux's CPACR_EL1, 0x310000 (FPEN 0b11 and ZEN 0b01),
# and its MDSCR_EL1, Isla exceeds 8 GB within 20 s, as it exceeds 16 GB with the control
# registers symbolic.
#
# Usage: tests/isla/svc-traces.sh el1|vhe [DIR]
# DIR defaults to tests/isla/linux-PROFILE.  The script writes DIR/svc.opcode and DIR/svc.trace and
# prints "svc SECONDS KIB", the elapsed time and the peak resident memory.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
profile=$1
dir=${2:-$here/linux-$profile}
probe=$HOME/isla-probe
isla=$probe/isla-patched/target/release/isla-footprint
export LD_LIBRARY_PATH=$probe/z3/install/lib
exec 3>&1
case $profile in
  el1) hcr=0x0000000480000000 el=1 ;;
  vhe) hcr=0x0000000488000038 el=2 ;;
  *)
    echo "unknown profile $profile" >&2
    exit 1 ;;
esac
mkdir -p "$dir"
irdir=${ISLA_IR:-$probe/ir}
args=(-A "$irdir/armv9p4-checked.ir" -C "$probe/isla-patched/configs/armv9p4.toml"
  -f isla_footprint_no_init -s --simplify-registers --tree -I __isla_vector_gpr=true
  -I __supported_pa_size=40)
while read -r setting; do
  args+=(-I "$setting")
done < "$here/kvm/features"
args+=(-R PSTATE.EL=0b00 -R PSTATE.SP=0b0
  -R "HCR_EL2={bits=$hcr}" -R "SCR_EL3={bits=0x0000000000000401}"
  -R "MDCR_EL2={bits=0x0000000000000000}" -R "VTCR_EL2={bits=0x0000000000000000}"
  -R "MDSCR_EL1={bits=0x0000000000000000}" -R "OSLSR_EL1={bits=0x0000000000000008}"
  -R "OSDLR_EL1={bits=0x0000000000000000}" -R "DBGPRCR_EL1={bits=0x0000000000000000}"
  -R "MDCCSR_EL0={bits=0x0000000000000000}" -R "_EDSCR={bits=0x02000002}"
  -R "ZCR_EL3={bits=0x0000000000000000}" -R "SMCR_EL3={bits=0x0000000000000000}"
  -R "ZCR_EL2={bits=0x0000000000000000}" -R "SMCR_EL2={bits=0x0000000000000000}"
  -R "ZCR_EL1={bits=0x0000000000000000}" -R "SMCR_EL1={bits=0x0000000000000000}"
  -R "HFGITR_EL2={bits=0x0000000000000000}"
  -R "SCTLR_EL$el=undefined:%struct SCTLR_EL${el}_Type"
  -R "TCR_EL$el=undefined:%struct TCR_EL${el}_Type" -R "VBAR_EL$el=undefined:%bv64")
opcode="11010100000000000000000000000001"
printf '%s\n' "$opcode" > "$dir/svc.opcode"
/usr/bin/time -f "svc %e %M" -o /dev/fd/3 \
  systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 -p CPUQuota=100% \
  timeout 1800 "$isla" "${args[@]}" --partial -i "$opcode" > "$dir/svc.trace"
