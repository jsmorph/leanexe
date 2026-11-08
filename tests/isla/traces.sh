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
# registers with Arm's feature constraints (AARCHMRS 2026-09), and
# __supported_pa_size is the guest's physical address size, 44 bits under tcg and 40 under kvm.
# The Sail model's HaveEL is true at every exception level, so the registers of EL2 and EL3 that
# the traces read take values that reproduce the profile: under tcg, EL2 and EL3 are absent, and
# every control that the traces test has the value that gives the absent level's effect; under
# kvm, the controls are those of KVM in Linux 7.0 and of Linux's boot protocol, except
# HCR_EL2.VM, whose second stage the trusted base covers, and SCR_EL3.EA and NMEA, which only the
# exception entry of the SP alignment fault tests and whose firmware values are unknown.  Runs with
# HCR_EL2, SCR_EL3, MDCR_EL2, and VTCR_EL2 symbolic except for the tested bits show no other bit
# tested, and the other bits are 0.  The debug registers, PSTATE.D, and PSTATE.PAN take QEMU's and
# KVM's reset values, which the startup leaves, except EDSCR.PipeAdv, which __InstructionExecute
# sets before the decode, where the traces start (fetch.sail 284 in the Sail model).  In both
# profiles, no other write before the decode changes a register that the traces read.  On the
# fault's exception entry, VBAR_EL1 is symbolic, and ZCR_EL3 and SMCR_EL3 are 0, Isla's
# configuration value, which keeps that path's vector length concrete.
#
# The features derive from these ID registers of the guests.  Every other ID_AA64 register reads
# 0 in both profiles, and under kvm only MIDR_EL1 and REVIDR_EL1 differ between the core types.
#   Register          tcg                 kvm
#   ID_AA64PFR0_EL1   0x0000000000000022  0x1101001121111111
#   ID_AA64PFR1_EL1   0x0                 0x0000000000000021
#   ID_AA64ZFR0_EL1   0x0                 0x0000110100110021
#   ID_AA64DFR0_EL1   0x0000000010305106  0x000000f010305609
#   ID_AA64ISAR0_EL1  0x0000000000011120  0x0221111110212120
#   ID_AA64ISAR1_EL1  0x0                 0x0111111100211002
#   ID_AA64ISAR2_EL1  0x0                 0x0000000000005102
#   ID_AA64MMFR0_EL1  0x0000000000001124  0x2100022200101122
#   ID_AA64MMFR1_EL1  0x0                 0x1000111010312122
#   ID_AA64MMFR2_EL1  0x0                 0x1221011110001011
#
# Edits apply to copies of the IR, and each diff's header states what it replaces.  Isla's harness
# function isla_footprint_common catches every exception that the decoder throws, so a path that
# ends in SEE, UNDEFINED, or UNPREDICTABLE would look complete.  tests/isla/armv9p4-checked.diff
# makes such an exception fail an assertion, which stops the run, and keeps the exception that every
# exception entry throws.  Every integer and memory form runs on armv9p4-checked.ir.  The Sail model
# computes UDIV's quotient by dividing real numbers, which Isla does not implement, so UDIV runs on
# armv9p4-checked-udiv.ir, which tests/isla/armv9p4-udiv.diff edits further to compute the quotient
# with Sail's tdiv_int on the same integers.  The floating-point forms run on
# armv9p4-checked-fp.ir, to which tests/isla/armv9p4-checked-fp.diff adds 64-bit wrappers of the
# floating-point functions, such as FPAdd64, called only at 64 bits, and the arithmetic forms,
# UCVTF, and FCVTZU leave their wrapper abstract with --abstract, since Arm's pseudocode rounds a
# real number.
# The copies sit beside the IR:
#   ir=~/isla-probe/ir && cp $ir/armv9p4.ir $ir/armv9p4-checked.ir &&
#   patch $ir/armv9p4-checked.ir < tests/isla/armv9p4-checked.diff &&
#   cp $ir/armv9p4-checked.ir $ir/armv9p4-checked-udiv.ir &&
#   patch $ir/armv9p4-checked-udiv.ir < tests/isla/armv9p4-udiv.diff &&
#   cp $ir/armv9p4-checked.ir $ir/armv9p4-checked-fp.ir &&
#   patch $ir/armv9p4-checked-fp.ir < tests/isla/armv9p4-checked-fp.diff
#
# The floating-point forms run with the startup's CPACR_EL1, 0x300000, FPEN 0b11, and FPCR,
# 0x02000000, DN set, and with the profile's CPTR_EL2 and CPTR_EL3, of which the traces test TFP
# under tcg and FPEN, ZEN, TFP, and EZ under kvm.  Under tcg both are 0, which gives the absent
# levels' effect.  Under kvm, CPTR_EL3 is 0x100, EZ set as Linux's boot protocol requires on a
# processor with SVE, and CPTR_EL2 is 0x50330000, which KVM in Linux 7.0 writes through CPACR_EL1
# under VHE once the guest owns the floating-point registers: TAM, TTA, FPEN 0b11, and ZEN 0b11 for
# a vCPU with SVE (__activate_cptr_traps_vhe, arch/arm64/kvm/hyp/include/hyp/switch.h).  Before
# that, KVM traps the guest's first floating-point instruction, loads the guest's registers, and
# resumes the guest at the instruction (kvm_hyp_handle_fpsimd).
#
# A third profile, sme, traces only the floating-point forms, with kvm's settings on a processor that
# also implements FEAT_SME and FEAT_SME_FA64, a check that their results do not depend on
# PSTATE.SM or SMCR_ELx.FA64, which Linux's boot protocol leaves free.  The traces leave PSTATE.SM,
# SMCR_EL1, and SMCR_EL2 unknown, and set what booting.rst requires of such a processor: ESM
# besides EZ in CPTR_EL3, 0x1100, SMEN 0b11 besides kvm's fields in CPTR_EL2, 0x53330000, and FA64
# in SMCR_EL3, 0x80000000, whose LEN, which booting.rst leaves to the firmware, is 0.
#
# Usage: tests/isla/traces.sh tcg|kvm|sme [DIR [FORM...]]
# DIR defaults to the profile's directory beside this script.  For each form, the script writes
# DIR/FORM.opcode, which holds on one line the pattern of the opcode's bits that it passes to Isla
# with -i, then writes DIR/FORM.trace and prints "FORM SECONDS KIB", the elapsed time and peak
# resident memory.  ISLA_IR names the directory of the IR copies, ~/isla-probe/ir unless set.  With
# PRINT_ARGS set to a directory, it writes DIR/FORM.opcode and each form's arguments to Isla,
# separated by NUL bytes, to PRINT_ARGS/FORM.args, and runs nothing.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
profile=$1
dir=${2:-$here/$profile}
shift $(($# < 2 ? $# : 2))
probe=$HOME/isla-probe
isla=$probe/isla-patched/target/release/isla-footprint
export LD_LIBRARY_PATH=$probe/z3/install/lib
exec 3>&1

smcr3=() fp_only=
case $profile in
  tcg)
    hcr=0x0000000080000000 oslsr=0x000000000000000a pa=44
    cptr2=0x0000000000000000 cptr3=0x0000000000000000 ;;
  kvm)
    hcr=0x0000000480000000 oslsr=0x0000000000000008 pa=40
    cptr2=0x0000000050330000 cptr3=0x0000000000000100 ;;
  sme)
    hcr=0x0000000480000000 oslsr=0x0000000000000008 pa=40
    cptr2=0x0000000053330000 cptr3=0x0000000000001100 fp_only=1
    smcr3=(-R "SMCR_EL3={bits=0x0000000080000000}") ;;
  *)
    echo "unknown profile $profile" >&2
    exit 1 ;;
esac
irdir=${ISLA_IR:-$probe/ir}
ir=$irdir/armv9p4-checked.ir
base=(-C "$probe/isla-patched/configs/armv9p4.toml"
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
  -R "MDCCSR_EL0={bits=0x0000000000000000}" -R "_EDSCR={bits=0x02000002}")
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
fp=("${tcr[@]}" -R "CPACR_EL1={bits=0x0000000000300000}" -R "CPTR_EL2={bits=$cptr2}"
  -R "CPTR_EL3={bits=$cptr3}" -R "FPCR={bits=0x0000000002000000}" "${smcr3[@]}")
dword="bvadd ($x) ((_ zero_extend 49) (concat imm12 #b000))"
byte="bvadd ($x) ((_ zero_extend 52) imm12)"

# run FORM OPCODE ARG...: OPCODE is the pattern that Isla's -i takes with --partial.
run() {
  local name=$1 opcode=$2
  shift 2
  if [ ${#only[@]} -gt 0 ] && ! printf '%s\n' "${only[@]}" | grep -qx "$name"; then
    return
  fi
  if [ -n "$fp_only" ] && [ "$ir" != "$irdir/armv9p4-checked-fp.ir" ]; then
    return
  fi
  local args=(-A "$ir" "${base[@]}" "$@" --partial -i "$opcode")
  printf '%s\n' "$opcode" > "$dir/$name.opcode"
  if [ -n "${PRINT_ARGS:-}" ]; then
    printf '%s\0' "${args[@]}" > "$PRINT_ARGS/$name.args"
    return
  fi
  /usr/bin/time -f "$name %e %M" -o /dev/fd/3 \
    systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 timeout 1800 \
    "$isla" "${args[@]}" > "$dir/$name.trace"
}
only=("$@")

run movz "110100101 hw:2 imm16:16 Rd:5" "${tcr[@]}"
run movk "111100101 hw:2 imm16:16 Rd:5" "${tcr[@]}"
run add-imm "1001000100 imm12:12 Rn:5 Rd:5" "${tcr[@]}" -L AddWithCarry
run sub-imm "1101000100 imm12:12 Rn:5 Rd:5" "${tcr[@]}" -L AddWithCarry
run subs-imm "1111000100 imm12:12 Rn:5 Rd:5" "${tcr[@]}" -L AddWithCarry
run subs-reg "11101011000 Rm:5 000000 Rn:5 Rd:5" "${tcr[@]}" -L AddWithCarry
run csinc "10011010100 Rm:5 cond:4 01 Rn:5 Rd:5" "${tcr[@]}" -L ConditionHolds
run orr-reg "10101010000 Rm:5 000000 Rn:5 Rd:5" "${tcr[@]}"
run lsr-imm "1101001101 immr:6 111111 Rn:5 Rd:5" "${tcr[@]}"
run ldr "1111100101 imm12:12 Rn:5 Rt:5" "${memory[@]}" \
  --reset-constraint "and (bvuge ($dword) 0x0000000040000000) (bvule ($dword) 0x000000007ffffff8)"
run str "1111100100 imm12:12 Rn:5 Rt:5" "${memory[@]}" \
  --reset-constraint "and (bvuge ($dword) 0x0000000040000000) (bvule ($dword) 0x000000007ffffff8)"
run strb "0011100100 imm12:12 Rn:5 Rt:5" "${memory[@]}" \
  --reset-constraint "and (bvuge ($byte) 0x0000000040000000) (bvule ($byte) 0x000000007fffffff)"
run strb-uart "0011100100 imm12:12 Rn:5 Rt:5" "${memory[@]}" \
  --reset-constraint "= ($byte) 0x0000000009000000"
run b "000101 imm26:26" "${branch[@]}"
run bl "100101 imm26:26" "${branch[@]}"
run cbz "10110100 imm19:19 Rt:5" "${branch[@]}"
run cbnz "10110101 imm19:19 Rt:5" "${branch[@]}"
run ret "1101011001011111000000 Rn:5 00000" "${branch[@]}"
run b-cond "01010100 imm19:19 0 cond:4" "${branch[@]}" -L ConditionHolds
run msub "10011011000 Rm:5 1 Ra:5 Rn:5 Rd:5" "${tcr[@]}"
run madd "10011011000 Rm:5 0 Ra:5 Rn:5 Rd:5" "${tcr[@]}"
run add-reg "10001011000 Rm:5 000000 Rn:5 Rd:5" "${tcr[@]}" -L AddWithCarry
run sub-reg "11001011000 Rm:5 000000 Rn:5 Rd:5" "${tcr[@]}" -L AddWithCarry
run and-reg "10001010000 Rm:5 000000 Rn:5 Rd:5" "${tcr[@]}"
run eor-reg "11001010000 Rm:5 000000 Rn:5 Rd:5" "${tcr[@]}"
run lslv "10011010110 Rm:5 001000 Rn:5 Rd:5" "${tcr[@]}"
run lsrv "10011010110 Rm:5 001001 Rn:5 Rd:5" "${tcr[@]}"
run orr-w "00101010000 Rm:5 000000 Rn:5 Rd:5" "${tcr[@]}"
run adr "0 immlo:2 10000 immhi:19 Rd:5" "${tcr[@]}"
run adrp "1 immlo:2 10000 immhi:19 Rd:5" "${tcr[@]}"
ir=$irdir/armv9p4-checked-udiv.ir
run udiv "10011010110 Rm:5 000010 Rn:5 Rd:5" "${tcr[@]}"
ir=$irdir/armv9p4-checked-fp.ir
run fmov-dx "1001111001100111000000 Rn:5 Rd:5" "${fp[@]}"
run fmov-xd "1001111001100110000000 Rn:5 Rd:5" "${fp[@]}"
run fadd "00011110011 Rm:5 001010 Rn:5 Rd:5" "${fp[@]}" --abstract FPAdd64
run fsub "00011110011 Rm:5 001110 Rn:5 Rd:5" "${fp[@]}" --abstract FPSub64
run fmul "00011110011 Rm:5 000010 Rn:5 Rd:5" "${fp[@]}" --abstract FPMul64
run fdiv "00011110011 Rm:5 000110 Rn:5 Rd:5" "${fp[@]}" --abstract FPDiv64
run fsqrt "0001111001100001110000 Rn:5 Rd:5" "${fp[@]}" --abstract FPSqrt64
run ucvtf "1001111001100011000000 Rn:5 Rd:5" "${fp[@]}" --abstract FixedToFP64
run fcvtzu "1001111001111001000000 Rn:5 Rd:5" "${fp[@]}" --abstract FPToFixed64
run fcmp "00011110011 Rm:5 001000 Rn:5 00000" "${fp[@]}" --abstract FPCompare
run fmov-sw "0001111000100111000000 Rn:5 Rd:5" "${fp[@]}"
run fmov-ws "0001111000100110000000 Rn:5 Rd:5" "${fp[@]}"
run fadd-s "00011110001 Rm:5 001010 Rn:5 Rd:5" "${fp[@]}" --abstract FPAdd32
run fsub-s "00011110001 Rm:5 001110 Rn:5 Rd:5" "${fp[@]}" --abstract FPSub32
run fmul-s "00011110001 Rm:5 000010 Rn:5 Rd:5" "${fp[@]}" --abstract FPMul32
run fdiv-s "00011110001 Rm:5 000110 Rn:5 Rd:5" "${fp[@]}" --abstract FPDiv32
run fsqrt-s "0001111000100001110000 Rn:5 Rd:5" "${fp[@]}" --abstract FPSqrt32
run frintn-s "0001111000100100010000 Rn:5 Rd:5" "${fp[@]}" --abstract FPRoundInt32
run ucvtf-sx "1001111000100011000000 Rn:5 Rd:5" "${fp[@]}" --abstract FixedToFP64_32
run scvtf-sw "0001111000100010000000 Rn:5 Rd:5" "${fp[@]}" --abstract FixedToFP32_32
run fcvtzu-xs "1001111000111001000000 Rn:5 Rd:5" "${fp[@]}" --abstract FPToFixed32_64
run fcvtzs-ws "0001111000111000000000 Rn:5 Rd:5" "${fp[@]}" --abstract FPToFixed32_32
run fcmp-s "00011110001 Rm:5 001000 Rn:5 00000" "${fp[@]}" --abstract FPCompare
