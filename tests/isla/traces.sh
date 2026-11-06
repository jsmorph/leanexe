#!/usr/bin/env bash
# The Isla traces of every instruction form of LeanExe/A64/Machine.lean other than the system
# forms, in one of two processor profiles: tcg, QEMU 8.2.2's Cortex-A57 under TCG, and kvm, the
# guest of KVM in Linux 7.0 on the Cortex-X925 and Cortex-A725 cores of edgexpert-18ff.  The
# traces come from the Armv9.4-A snapshot of the Sail model (isla-snapshots d8b31014, armv9p4.ir),
# Z3 4.12.6, and Isla e9b5d945 with tests/isla/isla-e9b5d945.patch applied, built in
# ~/isla-probe/isla-patched on edgexpert-18ff:
#   cp -a ~/isla-probe/isla ~/isla-probe/isla-patched && cd ~/isla-probe/isla-patched &&
#   patch -p1 < isla-e9b5d945.patch && PATH=$HOME/.cargo/bin:$PATH
#   LIBRARY_PATH=$HOME/isla-probe/z3/install/lib cargo build --release
#
# Every opcode field is symbolic, and Isla reads the general registers as a vector
# (__isla_vector_gpr), so register 31 is the only register number with paths of its own.  The
# entry point isla_footprint_no_init skips the reset, so every register that the configuration
# leaves unset is a fresh variable.  The processor runs at EL1 with SP_EL1 and the startup's
# SCTLR_EL1, TCR_EL1, and MAIR_EL1 (LeanExe/A64/Boot.lean: sctlrOn, tcrValue, mairValue); the
# branches leave TCR_EL1 symbolic.  -L AddWithCarry and -L ConditionHolds replace the flag
# computations of the forms that use them by Isla's linearized versions.
#
# The loads and stores keep TTBR0_EL1 (Sail's TTBR0_NS) symbolic over every 32-byte-aligned
# address in the RAM GiB, and the patch answers the walk's reads at TTBR0_EL1 and TTBR0_EL1 + 8
# with the startup's descriptors (LeanExe/A64/Table.lean), recording each as a read-mem event at
# the address that the walk computed.  A reset constraint, which the patch lets name the opcode's
# fields, keeps every byte of the access in the RAM GiB, X[Rn] being SP_EL1 for Rn = 31; the
# byte store's second trace, strb-uart, puts the access at the UART's data register 0x09000000,
# which descriptor 0 maps as Device memory.
#
# Each profile's directory holds its feature settings, `features`, derived from the guest's ID
# registers (devnotes.md lists them) with Arm's feature constraints (AARCHMRS 2026-09), and
# __supported_pa_size is the guest's physical address size, 44 bits under tcg and 40 under kvm.
# The Sail model's HaveEL is true at every exception level, so the registers of EL2 and EL3 that
# the traces read take values that reproduce the profile: under tcg, EL2 and EL3 are absent, and
# every control that the traces test has the value that gives the absent level's effect; under
# kvm, the controls are those of KVM in Linux 7.0 and of Linux's boot protocol, except
# HCR_EL2.VM, whose second stage the trusted base covers, and SCR_EL3.EA and NMEA, which only the
# exception entry of the SP alignment fault tests and whose firmware values are unknown.  Runs with
# HCR_EL2, SCR_EL3, MDCR_EL2, and VTCR_EL2 symbolic except for the tested bits show no other bit
# tested, and the other bits are 0.  The debug registers, PSTATE.D, and PSTATE.PAN take QEMU's and
# KVM's reset values, which the startup leaves.  On the fault's exception entry, VBAR_EL1 is
# symbolic, and ZCR_EL3 and SMCR_EL3 are 0, Isla's configuration value, which keeps that path's
# vector length concrete.
#
# UDIV has no trace: its specification divides as real numbers, which Isla cannot do with symbolic
# operands.
#
# Usage: tests/isla/traces.sh tcg|kvm [DIR [FORM...]]
# DIR defaults to the profile's directory beside this script.  For each form, the script writes
# DIR/FORM.trace and prints "FORM SECONDS KIB", the elapsed time and peak resident memory.  With
# PRINT_ARGS set to a directory, it writes each form's arguments to Isla, separated by NUL bytes,
# to PRINT_ARGS/FORM.args and runs nothing.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
profile=$1
dir=${2:-$here/$profile}
shift $(($# < 2 ? $# : 2))
probe=$HOME/isla-probe
isla=$probe/isla-patched/target/release/isla-footprint
export LD_LIBRARY_PATH=$probe/z3/install/lib
exec 3>&1

case $profile in
  tcg)
    hcr=0x0000000080000000 oslsr=0x000000000000000a pa=44 ;;
  kvm)
    hcr=0x0000000480000000 oslsr=0x0000000000000008 pa=40 ;;
  *)
    echo "unknown profile $profile" >&2
    exit 1 ;;
esac
base=(-A "$probe/ir/armv9p4.ir" -C "$probe/isla-patched/configs/armv9p4.toml"
  -f isla_footprint_no_init -s --simplify-registers --tree -I __isla_vector_gpr=true
  -I __supported_pa_size=$pa)
while read -r setting; do
  base+=(-I "$setting")
done < "$here/$profile/features"
base+=(-R PSTATE.EL=0b01 -R PSTATE.SP=0b1 -R PSTATE.D=0b1 -R PSTATE.PAN=0b0
  -R "SCTLR_EL1={bits=0x0000000030d0198d}" -R "MAIR_EL1={bits=0x000000000000ff00}"
  -R "HCR_EL2={bits=$hcr}" -R "SCR_EL3={bits=0x0000000000000401}"
  -R "MDCR_EL2={bits=0x0000000000000000}" -R "VTCR_EL2={bits=0x0000000000000000}"
  -R "MDSCR_EL1={bits=0x0000000000000000}" -R "OSLSR_EL1={bits=$oslsr}"
  -R "OSDLR_EL1={bits=0x0000000000000000}" -R "DBGPRCR_EL1={bits=0x0000000000000000}"
  -R "MDCCSR_EL0={bits=0x0000000000000000}" -R "_EDSCR={bits=0x00000002}")
tcr=(-R "TCR_EL1={bits=0x0000000080a03520}")
branch=(-R "TCR_EL1=undefined:%struct TCR_EL1_Type")

# X[Rn] for a load or store at EL1 with PSTATE.SP set.
x=R0
for r in $(seq 1 30); do
  bin=
  for i in 4 3 2 1 0; do
    bin+=$(((r >> i) & 1))
  done
  x="ite (= Rn #b$bin) R$r ($x)"
done
x="ite (= Rn #b11111) SP_EL1 ($x)"
memory=("${tcr[@]}" -R VBAR_EL1=undefined:%bv64 -R "ZCR_EL3={bits=0x0000000000000000}"
  -R "SMCR_EL3={bits=0x0000000000000000}"
  --reset-constraint "= (bvand TTBR0_NS.bits 0xffffffffc000001f) 0x0000000040000000"
  --fixed-memory "TTBR0_NS.bits=0x0060000000000401"
  --fixed-memory "bvadd TTBR0_NS.bits 0x0000000000000008=0x0040000040000705"
  --reset-constraint-fields)
dword="bvadd ($x) ((_ zero_extend 49) (concat imm12 #b000))"
byte="bvadd ($x) ((_ zero_extend 52) imm12)"

run() {
  local name=$1
  shift
  if [ ${#only[@]} -gt 0 ] && ! printf '%s\n' "${only[@]}" | grep -qx "$name"; then
    return
  fi
  if [ -n "${PRINT_ARGS:-}" ]; then
    printf '%s\0' "${base[@]}" "$@" > "$PRINT_ARGS/$name.args"
    return
  fi
  /usr/bin/time -f "$name %e %M" -o /dev/fd/3 \
    systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 timeout 1800 \
    "$isla" "${base[@]}" "$@" > "$dir/$name.trace"
}
only=("$@")

run movz "${tcr[@]}" --partial -i "110100101 hw:2 imm16:16 Rd:5"
run movk "${tcr[@]}" --partial -i "111100101 hw:2 imm16:16 Rd:5"
run add-imm "${tcr[@]}" -L AddWithCarry --partial -i "1001000100 imm12:12 Rn:5 Rd:5"
run sub-imm "${tcr[@]}" -L AddWithCarry --partial -i "1101000100 imm12:12 Rn:5 Rd:5"
run subs-imm "${tcr[@]}" -L AddWithCarry --partial -i "1111000100 imm12:12 Rn:5 Rd:5"
run subs-reg "${tcr[@]}" -L AddWithCarry --partial -i "11101011000 Rm:5 000000 Rn:5 Rd:5"
run csinc "${tcr[@]}" -L ConditionHolds --partial -i "10011010100 Rm:5 cond:4 01 Rn:5 Rd:5"
run orr-reg "${tcr[@]}" --partial -i "10101010000 Rm:5 000000 Rn:5 Rd:5"
run lsr-imm "${tcr[@]}" --partial -i "1101001101 immr:6 111111 Rn:5 Rd:5"
run ldr "${memory[@]}" --partial -i "1111100101 imm12:12 Rn:5 Rt:5" \
  --reset-constraint "and (bvuge ($dword) 0x0000000040000000) (bvule ($dword) 0x000000007ffffff8)"
run str "${memory[@]}" --partial -i "1111100100 imm12:12 Rn:5 Rt:5" \
  --reset-constraint "and (bvuge ($dword) 0x0000000040000000) (bvule ($dword) 0x000000007ffffff8)"
run strb "${memory[@]}" --partial -i "0011100100 imm12:12 Rn:5 Rt:5" \
  --reset-constraint "and (bvuge ($byte) 0x0000000040000000) (bvule ($byte) 0x000000007fffffff)"
run strb-uart "${memory[@]}" --partial -i "0011100100 imm12:12 Rn:5 Rt:5" \
  --reset-constraint "= ($byte) 0x0000000009000000"
run b "${branch[@]}" --partial -i "000101 imm26:26"
run bl "${branch[@]}" --partial -i "100101 imm26:26"
run cbz "${branch[@]}" --partial -i "10110100 imm19:19 Rt:5"
run cbnz "${branch[@]}" --partial -i "10110101 imm19:19 Rt:5"
run ret "${branch[@]}" --partial -i "1101011001011111000000 Rn:5 00000"
run b-cond "${branch[@]}" -L ConditionHolds --partial -i "01010100 imm19:19 0 cond:4"
run msub "${tcr[@]}" --partial -i "10011011000 Rm:5 1 Ra:5 Rn:5 Rd:5"
run madd "${tcr[@]}" --partial -i "10011011000 Rm:5 0 Ra:5 Rn:5 Rd:5"
run add-reg "${tcr[@]}" -L AddWithCarry --partial -i "10001011000 Rm:5 000000 Rn:5 Rd:5"
run sub-reg "${tcr[@]}" -L AddWithCarry --partial -i "11001011000 Rm:5 000000 Rn:5 Rd:5"
run and-reg "${tcr[@]}" --partial -i "10001010000 Rm:5 000000 Rn:5 Rd:5"
run eor-reg "${tcr[@]}" --partial -i "11001010000 Rm:5 000000 Rn:5 Rd:5"
run lslv "${tcr[@]}" --partial -i "10011010110 Rm:5 001000 Rn:5 Rd:5"
run lsrv "${tcr[@]}" --partial -i "10011010110 Rm:5 001001 Rn:5 Rd:5"
run orr-w "${tcr[@]}" --partial -i "00101010000 Rm:5 000000 Rn:5 Rd:5"
run adr "${tcr[@]}" --partial -i "0 immlo:2 10000 immhi:19 Rd:5"
run adrp "${tcr[@]}" --partial -i "1 immlo:2 10000 immhi:19 Rd:5"
