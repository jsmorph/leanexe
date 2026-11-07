#!/usr/bin/env bash
# The Isla traces of every instruction form of LeanExe/M7/Machine.lean, in AArch32 Thumb state at
# EL0 under an AArch64 EL1, from the Armv9.4-A snapshot of the Sail model (isla-snapshots d8b31014,
# armv9p4.ir), Z3 4.12.6, and the patched Isla of tests/isla/traces.sh, built in
# ~/isla-probe/isla-patched on edgexpert-18ff.  No machine-readable specification of the M-profile
# exists, so the traces check each form against the A-profile's AArch32 pseudocode.
#
# Two diffs make the IR of the traces.  tests/isla/armv9p4-t32.diff edits armv9p4-checked.ir so
# that the decode of B T3 takes its condition from the opcode's cond field, as CurrentCond() of
# DDI 0403E.e A7.3.1 does, and appends the harness functions isla_footprint_t32 and
# isla_footprint_t16, which do for a 32-bit and a 16-bit Thumb opcode what isla_footprint_no_init
# does for an A64 one.  tests/isla/armv9p4-t32-udiv.diff edits a copy for UDIV, whose quotient the
# Sail model computes by dividing real numbers.  Each diff's header states what it changes.  The
# copies sit beside the IR:
#   ir=~/isla-probe/ir && cp $ir/armv9p4-checked.ir $ir/armv9p4-t32.ir &&
#   patch $ir/armv9p4-t32.ir < tests/isla/armv9p4-t32.diff &&
#   cp $ir/armv9p4-t32.ir $ir/armv9p4-t32-udiv.ir &&
#   patch $ir/armv9p4-t32-udiv.ir < tests/isla/armv9p4-t32-udiv.diff
#
# A register field of a form of the model names r0 to r7, so each opcode below writes the top bit of
# a 4-bit register field as 0 and leaves the other three symbolic.  The processor runs in AArch32
# User mode in Thumb state outside an IT block, with the features of tests/isla/tcg/features, which
# implement AArch32 at EL0 and EL1, and with the EL2, EL3, and debug controls of that profile in
# tests/isla/traces.sh.  Isla reads the general registers as a vector (__isla_vector_gpr), so a
# symbolic register field adds no path.  -L AddWithCarry and -L ConditionHolds replace the flag
# computations by Isla's linearized versions.
#
# The loads and stores run with the stage 1 translation of the EL1&0 regime, which AArch32 EL0
# uses under an AArch64 EL1 with the VMSAv8-64 tables.  TCR_EL1 selects TTBR0_EL1 for the 32-bit
# virtual address space with the 4 KiB granule and a 36-bit physical address space, so the walk
# reads one level-1 descriptor for each GiB.  TTBR0_EL1 (Sail's TTBR0_NS) holds 0x100000000, above
# every address of the M7, and the patch's --fixed-memory answers the walk's reads there with two
# block descriptors: the GiB from 0, which holds DTCM at 0x20000000, as Normal memory, and the GiB
# from 0x40000000, which holds the device window, as Device-nGnRnE memory, both read-write at EL0.
# MAIR_EL1 gives attribute 0 Device-nGnRnE and attribute 1 Normal write-back, and SCTLR_EL1 is the
# A64 startup's value with alignment checks off.  A reset constraint, which the patch lets name the
# opcode's fields, keeps the access word-aligned and inside DTCM (the -dtcm forms) or inside the
# device window (the -dev forms), R[Rn] being R0 to R7, and SP (R13) for the SP-relative forms.
#
# Usage: tests/isla/m7-traces.sh [DIR [FORM...]]
# DIR defaults to tests/isla/m7, and IR_DIR, the directory of the two IR copies, to
# ~/isla-probe/ir.  For each form, the script writes DIR/FORM.opcode, which holds on one line the
# pattern of the opcode's bits that it passes to Isla with -i, then writes DIR/FORM.trace and
# prints "FORM SECONDS KIB", the elapsed time and peak resident memory.  With PRINT_ARGS set to a
# directory, it writes DIR/FORM.opcode and each form's arguments to Isla, separated by NUL bytes,
# to PRINT_ARGS/FORM.args, and runs nothing.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
dir=${1:-$here/m7}
shift $(($# < 1 ? $# : 1))
probe=$HOME/isla-probe
isla=$probe/isla-patched/target/release/isla-footprint
export LD_LIBRARY_PATH=$probe/z3/install/lib
exec 3>&1

irs=${IR_DIR:-$probe/ir}
ir=$irs/armv9p4-t32.ir
base=(-C "$probe/isla-patched/configs/armv9p4.toml" -s --simplify-registers --tree
  -I __isla_vector_gpr=true -I __supported_pa_size=44)
while read -r setting; do
  base+=(-I "$setting")
done < "$here/tcg/features"
base+=(-R PSTATE.nRW=0b1 -R PSTATE.T=0b1 -R PSTATE.EL=0b00 -R PSTATE.M=0b10000
  -R PSTATE.IT=0x00 -R PSTATE.E=0b0
  -R "HCR_EL2={bits=0x0000000080000000}" -R "SCR_EL3={bits=0x0000000000000401}"
  -R "MDCR_EL2={bits=0x0000000000000000}" -R "VTCR_EL2={bits=0x0000000000000000}"
  -R "MDSCR_EL1={bits=0x0000000000000000}" -R "OSLSR_EL1={bits=0x000000000000000a}"
  -R "OSDLR_EL1={bits=0x0000000000000000}" -R "DBGPRCR_EL1={bits=0x0000000000000000}"
  -R "MDCCSR_EL0={bits=0x0000000000000000}" -R "_EDSCR={bits=0x02000002}")

# R[Rn] for a 3-bit field Rn.
r=R0
for i in $(seq 1 7); do
  r="ite (= Rn #b$(((i >> 2) & 1))$(((i >> 1) & 1))$((i & 1))) R$i ($r)"
done
memory=(-R "SCTLR_EL1={bits=0x0000000030d0198d}" -R "MAIR_EL1={bits=0x000000000000ff00}"
  -R "TCR_EL1={bits=0x0000000180a03520}" -R "TTBR0_NS={bits=0x0000000100000000}"
  -R VBAR_EL1=undefined:%bv64 -R "ZCR_EL3={bits=0x0000000000000000}"
  -R "SMCR_EL3={bits=0x0000000000000000}"
  --fixed-memory "0x0000000100000000=0x0000000000000745"
  --fixed-memory "0x0000000100000008=0x0060000040000441"
  --reset-constraint-fields)
# The address of a word access, as a 64-bit value, and its constraints.
word() {
  local a="bvadd ((_ zero_extend 32) ((_ extract 31 0) ($1))) ((_ zero_extend 52) imm12)"
  local lo=$2 hi=$3
  echo "and (= ((_ extract 1 0) ($a)) #b00) (and (bvuge ($a) $lo) (bvule ($a) $hi))"
}
dtcm=(0x0000000020000000 0x000000002001fffc)
dev=(0x0000000040000000 0x000000004003fffc)

# run FORM FUNCTION OPCODE ARG...: OPCODE is the pattern that Isla's -i takes with --partial, and
# FUNCTION is t32 or t16.
run() {
  local name=$1 fn=$2 opcode=$3
  shift 3
  if [ ${#only[@]} -gt 0 ] && ! printf '%s\n' "${only[@]}" | grep -qx "$name"; then
    return
  fi
  local args=(-A "$ir" -f "isla_footprint_$fn" "${base[@]}" "$@" --partial -i "$opcode")
  printf '%s\n' "$opcode" > "$dir/$name.opcode"
  if [ -n "${PRINT_ARGS:-}" ]; then
    printf '%s\0' "${args[@]}" > "$PRINT_ARGS/$name.args"
    return
  fi
  /usr/bin/time -a -f "$name %e %M" -o /dev/fd/3 \
    systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 timeout 1800 \
    "$isla" "${args[@]}" > "$dir/$name.trace"
}
only=("$@")

run add-reg t32 "11101011000 S:1 0 Rn:3 0 imm3:3 0 Rd:3 imm2:2 00 0 Rm:3" -L AddWithCarry
run adc-reg t32 "1110101101000 Rn:3 00000 Rd:3 00000 Rm:3" -L AddWithCarry
run sub-reg t32 "11101011101 S:1 0 Rn:3 00000 Rd:3 00000 Rm:3" -L AddWithCarry
run sbc-reg t32 "11101011011 S:1 0 Rn:3 00000 Rd:3 00000 Rm:3" -L AddWithCarry
run and-reg t32 "1110101000000 Rn:3 00000 Rd:3 00000 Rm:3"
run orr-reg t32 "11101010010 S:1 0 Rn:3 00000 Rd:3 00000 Rm:3"
run eor-reg t32 "1110101010000 Rn:3 00000 Rd:3 00000 Rm:3"
run cmp-reg t32 "1110101110110 Rn:3 0000111100000 Rm:3" -L AddWithCarry
run lsl-reg t32 "1111101000000 Rn:3 11110 Rd:3 00000 Rm:3"
run lsr-reg t32 "1111101000100 Rn:3 11110 Rd:3 00000 Rm:3"
run lsl-imm t32 "11101010010011110 imm3:3 0 Rd:3 imm2:2 000 Rm:3"
run lsr-imm t32 "11101010010011110 imm3:3 0 Rd:3 imm2:2 010 Rm:3"
run sub-imm t32 "1111000110100 Rn:3 00000 Rd:3 imm8:8" -L AddWithCarry
run and-imm t32 "1111000000000 Rn:3 00000 Rd:3 imm8:8"
run eor-imm t32 "1111000010000 Rn:3 00000 Rd:3 imm8:8"
run cmp-imm t32 "1111000110110 Rn:3 00001111 imm8:8" -L AddWithCarry
run mov-imm t32 "111100000100111100000 Rd:3 imm8:8"
run movw t32 "11110 i:1 100100 imm4:4 0 imm3:3 0 Rd:3 imm8:8"
run movt t32 "11110 i:1 101100 imm4:4 0 imm3:3 0 Rd:3 imm8:8"
run addw-sp t32 "11110 i:1 1000001101 0 imm3:3 0 Rd:3 imm8:8" -L AddWithCarry
run subw-sp t32 "11110 i:1 1010101101 0 imm3:3 0 Rd:3 imm8:8" -L AddWithCarry
run addw-sp-sp t32 "11110 i:1 1000001101 0 imm3:3 1101 imm8:8" -L AddWithCarry
run subw-sp-sp t32 "11110 i:1 1010101101 0 imm3:3 1101 imm8:8" -L AddWithCarry
run clz t32 "1111101010110 Rm:3 11110 Rd:3 10000 Rm2:3" --reset-constraint-fields \
  --reset-constraint "= Rm Rm2"
run umull t32 "1111101110100 Rn:3 0 RdLo:3 0 RdHi:3 00000 Rm:3" --reset-constraint-fields \
  --reset-constraint "not (= RdLo RdHi)"
run mla t32 "1111101100000 Rn:3 0 Ra:3 0 Rd:3 00000 Rm:3"
run mls t32 "1111101100000 Rn:3 0 Ra:3 0 Rd:3 00010 Rm:3"
run ldr-dtcm t32 "1111100011010 Rn:3 0 Rt:3 imm12:12" "${memory[@]}" \
  --reset-constraint "$(word "$r" "${dtcm[@]}")"
run ldr-dev t32 "1111100011010 Rn:3 0 Rt:3 imm12:12" "${memory[@]}" \
  --reset-constraint "$(word "$r" "${dev[@]}")"
run str-dtcm t32 "1111100011000 Rn:3 0 Rt:3 imm12:12" "${memory[@]}" \
  --reset-constraint "$(word "$r" "${dtcm[@]}")"
run str-dev t32 "1111100011000 Rn:3 0 Rt:3 imm12:12" "${memory[@]}" \
  --reset-constraint "$(word "$r" "${dev[@]}")"
run ldr-sp t32 "11111000110111010 Rt:3 imm12:12" "${memory[@]}" \
  --reset-constraint "$(word R13 "${dtcm[@]}")"
run str-sp t32 "11111000110011010 Rt:3 imm12:12" "${memory[@]}" \
  --reset-constraint "$(word R13 "${dtcm[@]}")"
run ldr-lr t32 "11111000110111011110 imm12:12" "${memory[@]}" \
  --reset-constraint "$(word R13 "${dtcm[@]}")"
run str-lr t32 "11111000110011011110 imm12:12" "${memory[@]}" \
  --reset-constraint "$(word R13 "${dtcm[@]}")"
run b-cond t32 "11110 S:1 cond:4 imm6:6 10 J1:1 0 J2:1 imm11:11" -L ConditionHolds \
  --reset-constraint-fields --reset-constraint "bvule cond #b1101"
run b t32 "11110 S:1 imm10:10 10 J1:1 1 J2:1 imm11:11"
run bl t32 "11110 S:1 imm10:10 11 J1:1 1 J2:1 imm11:11"
run bx-lr t16 "0100011101110000"
run dsb t32 "11110011101111111000111101001111"
ir=$irs/armv9p4-t32-udiv.ir
run udiv t32 "1111101110110 Rn:3 11110 Rd:3 11110 Rm:3"
