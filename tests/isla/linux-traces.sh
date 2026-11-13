#!/usr/bin/env bash
# The Isla traces of a Linux process at EL0 (PSTATE.EL 0b00, PSTATE.SP 0b0, the state in which
# Linux runs a process, PSR_MODE_EL0t, arch/arm64/include/asm/processor.h line 339 of Linux 7.0)
# in one of two profiles of the kernel.  Under vhe, the host's kernel at EL2 with FEAT_VHE, under
# which HCR_EL2.{E2H, TGE} is {1, 1} and the registers of EL2 govern EL0, the script traces the
# forms of the A64 back end's Linux executables (LeanExe/A64/Linux.lean) whose behaviour depends
# on the exception level, and SVC #0.  Under el1, a kernel at EL1 under KVM on a host with VHE,
# with HCR_EL2.TGE clear, it traces SVC #0 alone.  The traces come from the Sail model, Isla, Z3,
# the IR copies, and the features of the profile kvm of tests/isla/traces.sh, those of the KVM
# guest on the host's cores, which lack FEAT_SPE: the host's cores implement it, and with it a
# taken branch and exception entry also update the sampling state of the Statistical Profiling
# Extension, which no form of the model reads.
#
# The registers of the kernel's or the firmware's configuration that a trace reads are symbolic,
# but for the debug registers OSLSR_EL1, OSDLR_EL1, DBGPRCR_EL1, MDCCSR_EL0, and _EDSCR, and
# VTCR_EL2, which take the values of traces.sh, and FPCR.  A reset constraint fixes some of their
# bits at the values that Linux 7.0 or the boot protocol gives them, and the traces cover every
# value of the bits that they test and no constraint fixes:
#   HCR_EL2.E2H (34) 1 and TGE (27) 1 under vhe, HCR_HOST_VHE_FLAGS (kvm_arm.h line 106); E2H 1,
#     TGE 0, and RW (31) 1 under el1, HCR_GUEST_FLAGS of a 64-bit guest (kvm_arm.h line 100 and
#     kvm_emulate.h line 107) on a host with VHE, where KVM sets E2H (arch/arm64/kvm/sys_regs.c
#     lines 5594 to 5595).
#   SCR_EL3.NS (0) 1 and RW (10) 1: the kernel runs in Non-secure state with AArch64 below EL3
#     (Documentation/arch/arm64/booting.rst).
#   For the floating-point forms, CPTR_EL2.{FPEN, ZEN} (21:20, 17:16), which E2H gives
#     CPACR_EL1's layout, at 0b11 and 0b01: floating point enabled at EL0 and EL1
#     (cpu_enable_fpsimd, arch/arm64/kernel/fpsimd.c lines 2026 to 2031) and SVE at EL1 alone
#     (line 1093), since exec clears TIF_SVE (fpsimd_flush_thread) and the program executes no SVE
#     instruction; CPTR_EL3.TFP (10) 0 (booting.rst); ZCR_EL2.LEN (3:0) 0, the vector length of
#     128 bits, which Linux writes through ZCR_EL1 under E2H (fpsimd.c line 1096) and which is
#     the only one that the host's cores implement; FPCR at 0x02000000, which the executable's
#     runtime writes first.
#   For SVC #0, MDCR_EL2.TDE (8) 0, which KVM sets only for a guest that its VMM debugs
#     (arch/arm64/kvm/debug.c line 57), MDSCR_EL1.SS (0) 0, no software step, which a tracer or a
#     uprobe sets, and HFGITR_EL2.SVC_EL0 (52) 0, no trap of SVC.  SCTLR_ELx, TCR_ELx, and
#     VBAR_ELx of the kernel's level and every field of PSTATE but EL, SP, and nRW are symbolic.
#     The trace leaves MaybeZeroSVEUppers abstract with --abstract: with SVE enabled at the
#     target level it zeroes, at each CONSTRAINED UNPREDICTABLE choice, the bits of Z0 to Z31
#     above the vector length, of P0 to P15, and of FFR, whose 2^49 paths exceed Isla's memory.
# The branches leave TCR_EL2 symbolic, as traces.sh leaves TCR_EL1.
#
# Usage: tests/isla/linux-traces.sh vhe|el1 [DIR [FORM...]]
# DIR defaults to tests/isla/linux-PROFILE.  For each form, the script writes DIR/FORM.opcode and
# DIR/FORM.trace and prints "FORM SECONDS KIB".  ISLA_IR names the directory of the IR copies,
# ~/isla-probe/ir unless set, which the commands of traces.sh make.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
profile=$1
dir=${2:-$here/linux-$profile}
shift $(($# < 2 ? $# : 2))
probe=$HOME/isla-probe
isla=$probe/isla-patched/target/release/isla-footprint
export LD_LIBRARY_PATH=$probe/z3/install/lib
case $profile in
  vhe) tge=1 el=2 ;;
  el1) tge=0 el=1 ;;
  *)
    echo "unknown profile $profile" >&2
    exit 1 ;;
esac
mkdir -p "$dir"
irdir=${ISLA_IR:-$probe/ir}
sym() {
  local r
  for r in "$@"; do
    printf '%s\0%s\0' -R "$r=undefined:%struct ${r}_Type"
  done
}
bit() {
  printf '%s\0%s\0' --reset-constraint "= ((_ extract $2 $2) $1.bits) #b$3"
}
field() {
  printf '%s\0%s\0' --reset-constraint "= ((_ extract $2 $3) $1.bits) #b$4"
}
mapfile -d '' base < <(
  printf '%s\0' -C "$probe/isla-patched/configs/armv9p4.toml" -f isla_footprint_no_init -s \
    --simplify-registers --tree -I __isla_vector_gpr=true -I __supported_pa_size=40
  while read -r setting; do
    printf '%s\0%s\0' -I "$setting"
  done < "$here/kvm/features"
  printf '%s\0' -R PSTATE.EL=0b00 -R PSTATE.SP=0b0 \
    -R "OSLSR_EL1={bits=0x0000000000000008}" -R "OSDLR_EL1={bits=0x0000000000000000}" \
    -R "DBGPRCR_EL1={bits=0x0000000000000000}" -R "MDCCSR_EL0={bits=0x0000000000000000}" \
    -R "_EDSCR={bits=0x02000002}" -R "VTCR_EL2={bits=0x0000000000000000}"
  sym HCR_EL2 SCR_EL3
  bit HCR_EL2 34 1
  bit HCR_EL2 27 "$tge"
  if [ "$profile" = el1 ]; then
    bit HCR_EL2 31 1
  fi
  bit SCR_EL3 0 1
  bit SCR_EL3 10 1)
mapfile -d '' branch < <(sym "TCR_EL$el")
mapfile -d '' fp < <(
  sym CPTR_EL2 CPTR_EL3 ZCR_EL2 ZCR_EL3 SMCR_EL2 SMCR_EL3
  field CPTR_EL2 21 20 11
  field CPTR_EL2 17 16 01
  bit CPTR_EL3 10 0
  field ZCR_EL2 3 0 0000
  field SMCR_EL3 3 0 0000
  printf '%s\0' -R "FPCR={bits=0x0000000002000000}")
mapfile -d '' svc < <(
  sym MDCR_EL2 MDSCR_EL1 HFGITR_EL2 "SCTLR_EL$el" "TCR_EL$el"
  printf '%s\0' -R "VBAR_EL$el=undefined:%bv64" --abstract MaybeZeroSVEUppers
  bit MDCR_EL2 8 0
  bit MDSCR_EL1 0 0
  bit HFGITR_EL2 52 0)

# run FORM IR OPCODE ARG...: OPCODE is the pattern that Isla's -i takes with --partial.
run() {
  local name=$1 ir=$2 opcode=$3
  shift 3
  if [ "$profile" = el1 ] && [ "$name" != svc ]; then
    return
  fi
  if [ ${#only[@]} -gt 0 ] && ! printf '%s\n' "${only[@]}" | grep -qx "$name"; then
    return
  fi
  printf '%s\n' "$opcode" > "$dir/$name.opcode"
  /usr/bin/time -f "$name %e %M" -o "$dir/$name.time" \
    systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 -p CPUQuota=100% \
    timeout 1800 "$isla" -A "$irdir/$ir" "${base[@]}" "$@" --partial -i "$opcode" \
    > "$dir/$name.trace"
  cat "$dir/$name.time"
  rm "$dir/$name.time"
}
only=("$@")
ck=armv9p4-checked.ir
fpir=armv9p4-checked-fp.ir

run svc $ck 11010100000000000000000000000001 "${svc[@]}"
run add-imm $ck "1001000100 imm12:12 Rn:5 Rd:5" -L AddWithCarry
run sub-imm $ck "1101000100 imm12:12 Rn:5 Rd:5" -L AddWithCarry
run subs-imm $ck "1111000100 imm12:12 Rn:5 Rd:5" -L AddWithCarry
run b $ck "000101 imm26:26" "${branch[@]}"
run bl $ck "100101 imm26:26" "${branch[@]}"
run cbz $ck "10110100 imm19:19 Rt:5" "${branch[@]}"
run cbnz $ck "10110101 imm19:19 Rt:5" "${branch[@]}"
run ret $ck "1101011001011111000000 Rn:5 00000" "${branch[@]}"
run b-cond $ck "01010100 imm19:19 0 cond:4" "${branch[@]}" -L ConditionHolds
run fmov-dx $fpir "1001111001100111000000 Rn:5 Rd:5" "${fp[@]}"
run fmov-xd $fpir "1001111001100110000000 Rn:5 Rd:5" "${fp[@]}"
run fadd $fpir "00011110011 Rm:5 001010 Rn:5 Rd:5" "${fp[@]}" --abstract FPAdd64
run fsub $fpir "00011110011 Rm:5 001110 Rn:5 Rd:5" "${fp[@]}" --abstract FPSub64
run fmul $fpir "00011110011 Rm:5 000010 Rn:5 Rd:5" "${fp[@]}" --abstract FPMul64
run fdiv $fpir "00011110011 Rm:5 000110 Rn:5 Rd:5" "${fp[@]}" --abstract FPDiv64
run fsqrt $fpir "0001111001100001110000 Rn:5 Rd:5" "${fp[@]}" --abstract FPSqrt64
run ucvtf $fpir "1001111001100011000000 Rn:5 Rd:5" "${fp[@]}" --abstract FixedToFP64
run fcvtzu $fpir "1001111001111001000000 Rn:5 Rd:5" "${fp[@]}" --abstract FPToFixed64
run fcmp $fpir "00011110011 Rm:5 001000 Rn:5 00000" "${fp[@]}" --abstract FPCompare
run fmov-sw $fpir "0001111000100111000000 Rn:5 Rd:5" "${fp[@]}"
run fmov-ws $fpir "0001111000100110000000 Rn:5 Rd:5" "${fp[@]}"
run fadd-s $fpir "00011110001 Rm:5 001010 Rn:5 Rd:5" "${fp[@]}" --abstract FPAdd32
run fsub-s $fpir "00011110001 Rm:5 001110 Rn:5 Rd:5" "${fp[@]}" --abstract FPSub32
run fmul-s $fpir "00011110001 Rm:5 000010 Rn:5 Rd:5" "${fp[@]}" --abstract FPMul32
run fdiv-s $fpir "00011110001 Rm:5 000110 Rn:5 Rd:5" "${fp[@]}" --abstract FPDiv32
run fsqrt-s $fpir "0001111000100001110000 Rn:5 Rd:5" "${fp[@]}" --abstract FPSqrt32
run frintn-s $fpir "0001111000100100010000 Rn:5 Rd:5" "${fp[@]}" --abstract FPRoundInt32
run ucvtf-sx $fpir "1001111000100011000000 Rn:5 Rd:5" "${fp[@]}" --abstract FixedToFP64_32
run scvtf-sw $fpir "0001111000100010000000 Rn:5 Rd:5" "${fp[@]}" --abstract FixedToFP32_32
run fcvtzu-xs $fpir "1001111000111001000000 Rn:5 Rd:5" "${fp[@]}" --abstract FPToFixed32_64
run fcvtzs-ws $fpir "0001111000111000000000 Rn:5 Rd:5" "${fp[@]}" --abstract FPToFixed32_32
run fcmp-s $fpir "00011110001 Rm:5 001000 Rn:5 00000" "${fp[@]}" --abstract FPCompare
