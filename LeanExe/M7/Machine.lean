/-!
A model of the Thumb-2 instructions that the Cortex-M7 back end emits, for a program in Thread
mode on one core, after the Armv7-M Architecture Reference Manual (DDI 0403E.e).  It covers 32-bit
data-processing forms on r0 to r7, `ADDW` and `SUBW` with SP, word loads and stores with a 12-bit
offset, conditional and unconditional branches, branch with link, `BX LR`, and `DSB SY`.

The code lies in a fixed map from addresses to halfwords, which a theorem derives from the image's
bytes, so a store never changes what the processor fetches.  `step` fetches the halfword at the
program counter and the one after it, decodes the instruction that starts there, and executes it.
A halfword whose bits 15 to 11 are 0b11101, 0b11110, or 0b11111 starts a 32-bit instruction, and
any other halfword is a 16-bit instruction (DDI 0403E.e section A5.1).  `decode` accepts exactly
the bit patterns that `encodeNat` gives the forms, so it rejects the register choices and the
values of should-be-one bits that the manual makes UNPREDICTABLE.

A word load or store needs an address that is a multiple of 4.  At an address that
`Platform.device` names, a load appends a read event with the next value of the sequence `σ` of
device values, and a store appends a write event.  At an address whose four bytes are Normal
memory, a load or store reads or writes memory.  `exec` returns `none` for every other access, for
`UDIV` with a zero divisor, and for `BX LR` with bit 0 of LR clear, which takes an INVSTATE
UsageFault on the processor (sections A7.7.20 and B3.2.15).  A theorem about a run that never
stops the model therefore excludes those states, whatever `CCR.DIV_0_TRP` and `CCR.UNALIGN_TRP`
hold.  The flags follow the pseudocode of `AddWithCarry` (section A2.2.1), and a write to SP clears
bits 1 and 0 of the value (section B1.4.7).  The model has no IT state, no exceptions, and no
floating-point registers, and the decoder accepts no IT, floating-point, or system instruction
other than `DSB SY`, which the model executes as a step to the next instruction.
-/

namespace LeanExe.M7

/-- Where loads and stores may go.  `normal a` holds when the byte at `a` is Normal memory that the
program may load and store, and `device a` when a word load or store at `a` is an access to a
device register. -/
structure Platform where
  normal : UInt32 → Bool
  device : UInt32 → Bool

/-- A device access: a word load from `a` that returned `v`, or a word store of `v` to `a`. -/
inductive Access where
  | read (a v : UInt32)
  | write (a v : UInt32)
  deriving DecidableEq, Repr

/-- The state that the emitted code uses: r0 to r12, SP, LR, the program counter, the condition
flags, the memory as bytes, the device accesses so far, and the number of device reads so far. -/
structure State where
  regs : Fin 13 → UInt32
  sp : UInt32
  lr : UInt32
  pc : UInt32
  nFlag : Bool
  zFlag : Bool
  cFlag : Bool
  vFlag : Bool
  mem : UInt32 → UInt8
  trace : List Access
  reads : Nat

/-- The instruction forms of the model.  A register field of type `Fin 8` names r0 to r7, and an
immediate field is the encoding's field: where an encoding splits an immediate, the constructor
carries the parts, and `exec` joins them.  Every form but `bxLr` is 32 bits wide. -/
inductive Instr where
  /-- `ADD{S}.W Rd, Rn, Rm, LSL #(4 * imm3 + imm2)` (A7.7.4, T3), which sets the flags when `s` is
  1. -/
  | addReg (s : Fin 2) (d n m : Fin 8) (imm3 : Fin 8) (imm2 : Fin 4)
  /-- `ADC.W Rd, Rn, Rm` (A7.7.2, T2). -/
  | adcReg (d n m : Fin 8)
  /-- `SUB{S}.W Rd, Rn, Rm` (A7.7.175, T2). -/
  | subReg (s : Fin 2) (d n m : Fin 8)
  /-- `SBC{S}.W Rd, Rn, Rm` (A7.7.125, T2). -/
  | sbcReg (s : Fin 2) (d n m : Fin 8)
  /-- `AND.W Rd, Rn, Rm` (A7.7.9, T2). -/
  | andReg (d n m : Fin 8)
  /-- `ORR{S}.W Rd, Rn, Rm` (A7.7.92, T2). -/
  | orrReg (s : Fin 2) (d n m : Fin 8)
  /-- `EOR.W Rd, Rn, Rm` (A7.7.36, T2). -/
  | eorReg (d n m : Fin 8)
  /-- `CMP.W Rn, Rm` (A7.7.28, T3). -/
  | cmpReg (n m : Fin 8)
  /-- `LSL.W Rd, Rn, Rm` (A7.7.69, T2), a shift by the bottom byte of Rm. -/
  | lslReg (d n m : Fin 8)
  /-- `LSR.W Rd, Rn, Rm` (A7.7.71, T2), a shift by the bottom byte of Rm. -/
  | lsrReg (d n m : Fin 8)
  /-- `LSL.W Rd, Rm, #(4 * imm3 + imm2)` (A7.7.68, T2), which is `MOV.W Rd, Rm` for 0. -/
  | lslImm (d m : Fin 8) (imm3 : Fin 8) (imm2 : Fin 4)
  /-- `LSR.W Rd, Rm, #(4 * imm3 + imm2)` (A7.7.70, T2), where 0 encodes a shift by 32. -/
  | lsrImm (d m : Fin 8) (imm3 : Fin 8) (imm2 : Fin 4)
  /-- `SUB.W Rd, Rn, #imm` (A7.7.174, T3), with the immediate's `i:imm3` 0000. -/
  | subImm (d n : Fin 8) (imm : Fin 256)
  /-- `AND.W Rd, Rn, #imm` (A7.7.8, T1), with the immediate's `i:imm3` 0000. -/
  | andImm (d n : Fin 8) (imm : Fin 256)
  /-- `EOR.W Rd, Rn, #imm` (A7.7.35, T1), with the immediate's `i:imm3` 0000. -/
  | eorImm (d n : Fin 8) (imm : Fin 256)
  /-- `CMP.W Rn, #imm` (A7.7.27, T2), with the immediate's `i:imm3` 0000. -/
  | cmpImm (n : Fin 8) (imm : Fin 256)
  /-- `MOV.W Rd, #imm` (A7.7.76, T2), with the immediate's `i:imm3` 0000. -/
  | movImm (d : Fin 8) (imm : Fin 256)
  /-- `MOVW Rd, #imm16` (A7.7.76, T3), where `imm16` is `imm4:i:imm3:imm8`. -/
  | movw (d : Fin 8) (imm4 : Fin 16) (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256)
  /-- `MOVT Rd, #imm16` (A7.7.79, T1), where `imm16` is `imm4:i:imm3:imm8`. -/
  | movt (d : Fin 8) (imm4 : Fin 16) (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256)
  /-- `ADDW Rd, SP, #imm12` (A7.7.5, T4), where `imm12` is `i:imm3:imm8`. -/
  | addwSp (d : Fin 8) (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256)
  /-- `SUBW Rd, SP, #imm12` (A7.7.176, T3), where `imm12` is `i:imm3:imm8`. -/
  | subwSp (d : Fin 8) (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256)
  /-- `ADDW SP, SP, #imm12` (A7.7.5, T4), where `imm12` is `i:imm3:imm8`. -/
  | addwSpSp (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256)
  /-- `SUBW SP, SP, #imm12` (A7.7.176, T3), where `imm12` is `i:imm3:imm8`. -/
  | subwSpSp (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256)
  /-- `CLZ Rd, Rm` (A7.7.24, T1). -/
  | clz (d m : Fin 8)
  /-- `UMULL RdLo, RdHi, Rn, Rm` (A7.7.204, T1), whose destinations differ. -/
  | umull (lo hi n m : Fin 8) (h : lo ≠ hi)
  /-- `MLA Rd, Rn, Rm, Ra` (A7.7.74, T1), which computes `Ra + Rn * Rm`. -/
  | mla (d n m a : Fin 8)
  /-- `MLS Rd, Rn, Rm, Ra` (A7.7.75, T1), which computes `Ra - Rn * Rm`. -/
  | mls (d n m a : Fin 8)
  /-- `UDIV Rd, Rn, Rm` (A7.7.195, T1). -/
  | udiv (d n m : Fin 8)
  /-- `LDR.W Rt, [Rn, #imm]` (A7.7.43, T3). -/
  | ldr (t n : Fin 8) (imm : Fin 4096)
  /-- `STR.W Rt, [Rn, #imm]` (A7.7.161, T3). -/
  | str (t n : Fin 8) (imm : Fin 4096)
  /-- `LDR.W Rt, [SP, #imm]` (A7.7.43, T3). -/
  | ldrSp (t : Fin 8) (imm : Fin 4096)
  /-- `STR.W Rt, [SP, #imm]` (A7.7.161, T3). -/
  | strSp (t : Fin 8) (imm : Fin 4096)
  /-- `LDR.W LR, [SP, #imm]` (A7.7.43, T3). -/
  | ldrLr (imm : Fin 4096)
  /-- `STR.W LR, [SP, #imm]` (A7.7.161, T3). -/
  | strLr (imm : Fin 4096)
  /-- `B<cond>.W` (A7.7.12, T3) to the program counter plus 4 plus `S:J2:J1:imm6:imm11:'0'` read as
  a signed 21-bit number, for the conditions EQ to LE, 0 to 13. -/
  | bcond (cond : Fin 14) (s j1 j2 : Fin 2) (imm6 : Fin 64) (imm11 : Fin 2048)
  /-- `B.W` (A7.7.12, T4) to the program counter plus 4 plus `S:I1:I2:imm10:imm11:'0'` read as a
  signed 25-bit number, where `I1` is `NOT(J1 EOR S)` and `I2` is `NOT(J2 EOR S)`. -/
  | b (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048)
  /-- `BL` (A7.7.18, T1), with the offset of `B.W`. -/
  | bl (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048)
  /-- `BX LR` (A7.7.20, T1), the only 16-bit form. -/
  | bxLr
  /-- `DSB SY` (A7.7.34, T1). -/
  | dsb

/-- The values of the halfwords of the instruction `i`, from the encoding diagrams of DDI 0403E.e
chapter A7: each is the form's fixed bits plus its fields at their positions, as a sum of natural
numbers.  The second component of the 16-bit form is 0. -/
def encodeNat : Instr → Nat × Nat
  | .addReg s d n m imm3 imm2 =>
      (0xEB00 + s.val * 16 + n.val, imm3.val * 4096 + d.val * 256 + imm2.val * 64 + m.val)
  | .adcReg d n m => (0xEB40 + n.val, d.val * 256 + m.val)
  | .subReg s d n m => (0xEBA0 + s.val * 16 + n.val, d.val * 256 + m.val)
  | .sbcReg s d n m => (0xEB60 + s.val * 16 + n.val, d.val * 256 + m.val)
  | .andReg d n m => (0xEA00 + n.val, d.val * 256 + m.val)
  | .orrReg s d n m => (0xEA40 + s.val * 16 + n.val, d.val * 256 + m.val)
  | .eorReg d n m => (0xEA80 + n.val, d.val * 256 + m.val)
  | .cmpReg n m => (0xEBB0 + n.val, 0x0F00 + m.val)
  | .lslReg d n m => (0xFA00 + n.val, 0xF000 + d.val * 256 + m.val)
  | .lsrReg d n m => (0xFA20 + n.val, 0xF000 + d.val * 256 + m.val)
  | .lslImm d m imm3 imm2 => (0xEA4F, imm3.val * 4096 + d.val * 256 + imm2.val * 64 + m.val)
  | .lsrImm d m imm3 imm2 =>
      (0xEA4F, imm3.val * 4096 + d.val * 256 + imm2.val * 64 + 0x10 + m.val)
  | .subImm d n imm => (0xF1A0 + n.val, d.val * 256 + imm.val)
  | .andImm d n imm => (0xF000 + n.val, d.val * 256 + imm.val)
  | .eorImm d n imm => (0xF080 + n.val, d.val * 256 + imm.val)
  | .cmpImm n imm => (0xF1B0 + n.val, 0x0F00 + imm.val)
  | .movImm d imm => (0xF04F, d.val * 256 + imm.val)
  | .movw d imm4 i imm3 imm8 =>
      (0xF240 + i.val * 1024 + imm4.val, imm3.val * 4096 + d.val * 256 + imm8.val)
  | .movt d imm4 i imm3 imm8 =>
      (0xF2C0 + i.val * 1024 + imm4.val, imm3.val * 4096 + d.val * 256 + imm8.val)
  | .addwSp d i imm3 imm8 => (0xF20D + i.val * 1024, imm3.val * 4096 + d.val * 256 + imm8.val)
  | .subwSp d i imm3 imm8 => (0xF2AD + i.val * 1024, imm3.val * 4096 + d.val * 256 + imm8.val)
  | .addwSpSp i imm3 imm8 => (0xF20D + i.val * 1024, imm3.val * 4096 + 0x0D00 + imm8.val)
  | .subwSpSp i imm3 imm8 => (0xF2AD + i.val * 1024, imm3.val * 4096 + 0x0D00 + imm8.val)
  | .clz d m => (0xFAB0 + m.val, 0xF080 + d.val * 256 + m.val)
  | .umull lo hi n m _ => (0xFBA0 + n.val, lo.val * 4096 + hi.val * 256 + m.val)
  | .mla d n m a => (0xFB00 + n.val, a.val * 4096 + d.val * 256 + m.val)
  | .mls d n m a => (0xFB00 + n.val, a.val * 4096 + d.val * 256 + 0x10 + m.val)
  | .udiv d n m => (0xFBB0 + n.val, 0xF0F0 + d.val * 256 + m.val)
  | .ldr t n imm => (0xF8D0 + n.val, t.val * 4096 + imm.val)
  | .str t n imm => (0xF8C0 + n.val, t.val * 4096 + imm.val)
  | .ldrSp t imm => (0xF8DD, t.val * 4096 + imm.val)
  | .strSp t imm => (0xF8CD, t.val * 4096 + imm.val)
  | .ldrLr imm => (0xF8DD, 0xE000 + imm.val)
  | .strLr imm => (0xF8CD, 0xE000 + imm.val)
  | .bcond cond s j1 j2 imm6 imm11 =>
      (0xF000 + s.val * 1024 + cond.val * 64 + imm6.val,
        0x8000 + j1.val * 8192 + j2.val * 2048 + imm11.val)
  | .b s j1 j2 imm10 imm11 =>
      (0xF000 + s.val * 1024 + imm10.val, 0x9000 + j1.val * 8192 + j2.val * 2048 + imm11.val)
  | .bl s j1 j2 imm10 imm11 =>
      (0xF000 + s.val * 1024 + imm10.val, 0xD000 + j1.val * 8192 + j2.val * 2048 + imm11.val)
  | .bxLr => (0x4770, 0)
  | .dsb => (0xF3BF, 0x8F4F)

/-- The field `x % n` as an element of `Fin n`. -/
def field (n x : Nat) (h : 0 < n := by decide) : Fin n := ⟨x % n, Nat.mod_lt x h⟩

/-- `UMULL` with the given fields when its destinations differ, and nothing otherwise. -/
def umullForms (lo hi n m : Fin 8) : List Instr :=
  if h : lo = hi then [] else [.umull lo hi n m h]

/-- One instruction of each 32-bit form, with the fields read from the halfwords `v1` and `v2` at
the form's positions, all fields reduced to the constructors' ranges. -/
def wideForms (v1 v2 : Nat) : List Instr :=
  let s := field 2 (v1 / 16)
  let n := field 8 v1
  let i := field 2 (v1 / 1024)
  let imm4 := field 16 v1
  let cond := field 14 (v1 / 64 % 16)
  let imm6 := field 64 v1
  let imm10 := field 1024 v1
  let t := field 8 (v2 / 4096)
  let d := field 8 (v2 / 256)
  let m := field 8 v2
  let imm2 := field 4 (v2 / 64)
  let imm8 := field 256 v2
  let imm12 := field 4096 v2
  let imm11 := field 2048 v2
  let j1 := field 2 (v2 / 8192)
  let j2 := field 2 (v2 / 2048)
  [.addReg s d n m t imm2, .adcReg d n m, .subReg s d n m, .sbcReg s d n m, .andReg d n m,
    .orrReg s d n m, .eorReg d n m, .cmpReg n m, .lslReg d n m, .lsrReg d n m,
    .lslImm d m t imm2, .lsrImm d m t imm2, .subImm d n imm8, .andImm d n imm8, .eorImm d n imm8,
    .cmpImm n imm8, .movImm d imm8, .movw d imm4 i t imm8, .movt d imm4 i t imm8,
    .addwSp d i t imm8, .subwSp d i t imm8, .addwSpSp i t imm8, .subwSpSp i t imm8, .clz d m,
    .mla d n m t, .mls d n m t, .udiv d n m, .ldr t n imm12, .str t n imm12, .ldrSp t imm12,
    .strSp t imm12, .ldrLr imm12, .strLr imm12, .bcond cond i j1 j2 imm6 imm11,
    .b i j1 j2 imm10 imm11, .bl i j1 j2 imm10 imm11, .dsb] ++ umullForms t d n m

/-- The 16-bit forms. -/
def narrowForms : List Instr := [.bxLr]

/-- The halfword of value `h` starts a 32-bit instruction. -/
def wide (h : Nat) : Prop := 29 ≤ h / 2048

instance (h : Nat) : Decidable (wide h) := inferInstanceAs (Decidable (29 ≤ h / 2048))

/-- The instruction whose encoding starts the halfwords, and the number of its halfwords, or `none`
when no form's `encodeNat` equals them. -/
def decode : List UInt16 → Option (Instr × Nat)
  | [] => none
  | h1 :: rest =>
      if wide h1.toNat then
        match rest with
        | [] => none
        | h2 :: _ =>
            ((wideForms h1.toNat h2.toNat).find? fun c =>
              encodeNat c == (h1.toNat, h2.toNat)).map fun i => (i, 2)
      else (narrowForms.find? fun c => (encodeNat c).1 == h1.toNat).map fun i => (i, 1)

namespace State

/-- Register `r` of r0 to r7. -/
def r (s : State) (r : Fin 8) : UInt32 :=
  s.regs ⟨r.val, by have := r.isLt; omega⟩

/-- The state with register `r` of r0 to r7 set to `v`. -/
def setR (s : State) (r : Fin 8) (v : UInt32) : State :=
  { s with regs := fun i => if i.val = r.val then v else s.regs i }

/-- The state with N and Z from the result `f.1`, C from `f.2.1`, and V from `f.2.2`. -/
def setNZCV (s : State) (f : UInt32 × Bool × Bool) : State :=
  { s with nFlag := f.1 >>> 31 == 1, zFlag := f.1 == 0, cFlag := f.2.1, vFlag := f.2.2 }

/-- The state after a form writes the result `f.1` to `d` and, when `sf` is 1, sets the flags from
`f`. -/
def result (s : State) (sf : Fin 2) (d : Fin 8) (f : UInt32 × Bool × Bool) : State :=
  if sf.val = 1 then (s.setR d f.1).setNZCV f else s.setR d f.1

/-- `ConditionPassed` of DDI 0403E.e section A7.3 for the condition `cond`, EQ to LE. -/
def condHolds (s : State) (cond : Fin 14) : Bool :=
  let r := match cond.val / 2 with
    | 0 => s.zFlag
    | 1 => s.cFlag
    | 2 => s.nFlag
    | 3 => s.vFlag
    | 4 => s.cFlag && !s.zFlag
    | 5 => s.nFlag == s.vFlag
    | _ => s.nFlag == s.vFlag && !s.zFlag
  if cond.val % 2 = 1 then !r else r

end State

/-- The word `x` read as a two's complement number. -/
def sint (x : UInt32) : Int :=
  if x.toNat < 2147483648 then x.toNat else (x.toNat : Int) - 4294967296

/-- `AddWithCarry` of DDI 0403E.e section A2.2.1: the low 32 bits of `x + y + c`, the carry out,
which is set when the unsigned sum does not fit 32 bits, and the overflow, which is set when the
signed sum does not. -/
def addWithCarry (x y : UInt32) (c : Bool) : UInt32 × Bool × Bool :=
  let u := x.toNat + y.toNat + c.toNat
  let r := UInt32.ofNat u
  (r, r.toNat != u, sint r != sint x + sint y + c.toNat)

/-- `x` shifted left by `k`, which is 0 for `k` from 32 up (`LSL_C`, section A2.2.1). -/
def shl (x : UInt32) (k : Nat) : UInt32 := if k < 32 then x <<< UInt32.ofNat k else 0

/-- `x` shifted right by `k`, which is 0 for `k` from 32 up (`LSR_C`, section A2.2.1). -/
def shr (x : UInt32) (k : Nat) : UInt32 := if k < 32 then x >>> UInt32.ofNat k else 0

/-- The number of leading zero bits of `x`, 32 for 0 (`CountLeadingZeroBits`, section A7.7.24). -/
def clz32 (x : UInt32) : UInt32 := if x = 0 then 32 else UInt32.ofNat (31 - x.toNat.log2)

/-- The field `v` of `bits` bits read as a two's complement number, as a 32-bit word. -/
def sext (bits v : Nat) : UInt32 :=
  if v < 2 ^ (bits - 1) then UInt32.ofNat v else UInt32.ofNat v - UInt32.ofNat (2 ^ bits)

/-- The immediate `i:imm3:imm8` of `ADDW` and `SUBW`. -/
def imm12 (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256) : UInt32 :=
  UInt32.ofNat (i.val * 2048 + imm3.val * 256 + imm8.val)

/-- The immediate `imm4:i:imm3:imm8` of `MOVW` and `MOVT`. -/
def imm16 (imm4 : Fin 16) (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256) : UInt32 :=
  UInt32.ofNat (imm4.val * 4096 + i.val * 2048 + imm3.val * 256 + imm8.val)

/-- The offset of `B<cond>.W`: `S:J2:J1:imm6:imm11:'0'` sign-extended from 21 bits. -/
def bcondOffset (s j1 j2 : Fin 2) (imm6 : Fin 64) (imm11 : Fin 2048) : UInt32 :=
  sext 21 (s.val * 1048576 + j2.val * 524288 + j1.val * 262144 + imm6.val * 4096 + imm11.val * 2)

/-- The offset of `B.W` and `BL`: `S:I1:I2:imm10:imm11:'0'` sign-extended from 25 bits, where `I1`
is `NOT(J1 EOR S)` and `I2` is `NOT(J2 EOR S)`. -/
def branchOffset (s j1 j2 : Fin 2) (imm10 : Fin 1024) (imm11 : Fin 2048) : UInt32 :=
  let i1 := 1 - (j1.val + s.val) % 2
  let i2 := 1 - (j2.val + s.val) % 2
  sext 25 (s.val * 16777216 + i1 * 8388608 + i2 * 4194304 + imm10.val * 4096 + imm11.val * 2)

/-- The four bytes from `a`, the lowest first, as a word. -/
def load32 (m : UInt32 → UInt8) (a : UInt32) : UInt32 :=
  (m a).toUInt32 ||| (m (a + 1)).toUInt32 <<< 8 ||| (m (a + 2)).toUInt32 <<< 16 |||
    (m (a + 3)).toUInt32 <<< 24

/-- The memory `m` with the four bytes from `a` replaced by those of `v`, the lowest first. -/
def store32 (m : UInt32 → UInt8) (a v : UInt32) : UInt32 → UInt8 :=
  fun b => if b - a < 4 then (v >>> ((b - a) * 8)).toUInt8 else m b

/-- Every one of the `k` bytes from `a` is Normal memory. -/
def Platform.mapped (P : Platform) (a : UInt32) (k : Nat) : Bool :=
  (List.range k).all fun i => P.normal (a + UInt32.ofNat i)

/-- A word load from `a`: the value and the state after it, or `none` when the model stops.  A
load from a device address takes the next value of the device sequence `σ` and records it. -/
def loadWord (P : Platform) (σ : Nat → UInt32) (s : State) (a : UInt32) :
    Option (UInt32 × State) :=
  if a % 4 ≠ 0 then none
  else if P.device a then
    some (σ s.reads, { s with trace := s.trace ++ [.read a (σ s.reads)], reads := s.reads + 1 })
  else if P.mapped a 4 then some (load32 s.mem a, s)
  else none

/-- A word store of `v` to `a`: the state after it, or `none` when the model stops. -/
def storeWord (P : Platform) (s : State) (a v : UInt32) : Option State :=
  if a % 4 ≠ 0 then none
  else if P.device a then some { s with trace := s.trace ++ [.write a v] }
  else if P.mapped a 4 then some { s with mem := store32 s.mem a v }
  else none

/-- The state after the instruction `i` at the program counter, or `none` when the model stops.
`σ` gives the values of the device reads in order.  Every form that does not branch is 32 bits
wide, so the next instruction lies at the program counter plus 4, and the value of the PC that a
branch adds its offset to is the instruction's address plus 4 (section B1.4.7). -/
def exec (P : Platform) (σ : Nat → UInt32) (i : Instr) (s : State) : Option State :=
  let next := s.pc + 4
  match i with
  | .addReg sf d n m imm3 imm2 =>
      some { s.result sf d (addWithCarry (s.r n) (shl (s.r m) (4 * imm3.val + imm2.val)) false)
        with pc := next }
  | .adcReg d n m => some { s.setR d (addWithCarry (s.r n) (s.r m) s.cFlag).1 with pc := next }
  | .subReg sf d n m =>
      some { s.result sf d (addWithCarry (s.r n) (~~~(s.r m)) true) with pc := next }
  | .sbcReg sf d n m =>
      some { s.result sf d (addWithCarry (s.r n) (~~~(s.r m)) s.cFlag) with pc := next }
  | .andReg d n m => some { s.setR d (s.r n &&& s.r m) with pc := next }
  | .orrReg sf d n m => some { s.result sf d (s.r n ||| s.r m, s.cFlag, s.vFlag) with pc := next }
  | .eorReg d n m => some { s.setR d (s.r n ^^^ s.r m) with pc := next }
  | .cmpReg n m => some { s.setNZCV (addWithCarry (s.r n) (~~~(s.r m)) true) with pc := next }
  | .lslReg d n m => some { s.setR d (shl (s.r n) ((s.r m).toNat % 256)) with pc := next }
  | .lsrReg d n m => some { s.setR d (shr (s.r n) ((s.r m).toNat % 256)) with pc := next }
  | .lslImm d m imm3 imm2 =>
      some { s.setR d (shl (s.r m) (4 * imm3.val + imm2.val)) with pc := next }
  | .lsrImm d m imm3 imm2 =>
      let k := 4 * imm3.val + imm2.val
      some { s.setR d (shr (s.r m) (if k = 0 then 32 else k)) with pc := next }
  | .subImm d n imm =>
      some { s.setR d (addWithCarry (s.r n) (~~~(UInt32.ofNat imm.val)) true).1 with pc := next }
  | .andImm d n imm => some { s.setR d (s.r n &&& UInt32.ofNat imm.val) with pc := next }
  | .eorImm d n imm => some { s.setR d (s.r n ^^^ UInt32.ofNat imm.val) with pc := next }
  | .cmpImm n imm =>
      some { s.setNZCV (addWithCarry (s.r n) (~~~(UInt32.ofNat imm.val)) true) with pc := next }
  | .movImm d imm => some { s.setR d (UInt32.ofNat imm.val) with pc := next }
  | .movw d imm4 i imm3 imm8 => some { s.setR d (imm16 imm4 i imm3 imm8) with pc := next }
  | .movt d imm4 i imm3 imm8 =>
      some { s.setR d (s.r d &&& (0xFFFF : UInt32) ||| imm16 imm4 i imm3 imm8 <<< (16 : UInt32)) with pc := next }
  | .addwSp d i imm3 imm8 =>
      some { s.setR d (addWithCarry s.sp (imm12 i imm3 imm8) false).1 with pc := next }
  | .subwSp d i imm3 imm8 =>
      some { s.setR d (addWithCarry s.sp (~~~(imm12 i imm3 imm8)) true).1 with pc := next }
  | .addwSpSp i imm3 imm8 =>
      some { s with
        sp := (addWithCarry s.sp (imm12 i imm3 imm8) false).1 &&& 0xFFFFFFFC
        pc := next }
  | .subwSpSp i imm3 imm8 =>
      some { s with
        sp := (addWithCarry s.sp (~~~(imm12 i imm3 imm8)) true).1 &&& 0xFFFFFFFC
        pc := next }
  | .clz d m => some { s.setR d (clz32 (s.r m)) with pc := next }
  | .umull lo hi n m _ =>
      let p := (s.r n).toNat * (s.r m).toNat
      some { (s.setR hi (UInt32.ofNat (p / 4294967296))).setR lo (UInt32.ofNat p) with pc := next }
  | .mla d n m a => some { s.setR d (s.r a + s.r n * s.r m) with pc := next }
  | .mls d n m a => some { s.setR d (s.r a - s.r n * s.r m) with pc := next }
  | .udiv d n m => if s.r m = 0 then none else some { s.setR d (s.r n / s.r m) with pc := next }
  | .ldr t n imm =>
      (loadWord P σ s (s.r n + UInt32.ofNat imm.val)).map fun (v, u) =>
        { u.setR t v with pc := next }
  | .str t n imm =>
      (storeWord P s (s.r n + UInt32.ofNat imm.val) (s.r t)).map fun u => { u with pc := next }
  | .ldrSp t imm =>
      (loadWord P σ s (s.sp + UInt32.ofNat imm.val)).map fun (v, u) =>
        { u.setR t v with pc := next }
  | .strSp t imm =>
      (storeWord P s (s.sp + UInt32.ofNat imm.val) (s.r t)).map fun u => { u with pc := next }
  | .ldrLr imm =>
      (loadWord P σ s (s.sp + UInt32.ofNat imm.val)).map fun (v, u) =>
        { u with lr := v, pc := next }
  | .strLr imm =>
      (storeWord P s (s.sp + UInt32.ofNat imm.val) s.lr).map fun u => { u with pc := next }
  | .bcond cond sb j1 j2 imm6 imm11 =>
      some { s with
        pc := if s.condHolds cond then s.pc + 4 + bcondOffset sb j1 j2 imm6 imm11 else next }
  | .b sb j1 j2 imm10 imm11 => some { s with pc := s.pc + 4 + branchOffset sb j1 j2 imm10 imm11 }
  | .bl sb j1 j2 imm10 imm11 =>
      some { s with lr := next ||| 1, pc := s.pc + 4 + branchOffset sb j1 j2 imm10 imm11 }
  | .bxLr => if s.lr % 2 = 1 then some { s with pc := s.lr &&& 0xFFFFFFFE } else none
  | .dsb => some { s with pc := next }

/-- One step from `s` with the code `code` and the device values `σ`: the fetch of the halfwords at
the program counter, the decoding, and the execution. -/
def step (P : Platform) (σ : Nat → UInt32) (code : UInt32 → Option UInt16) (s : State) :
    Option State := do
  let h ← code s.pc
  let (i, _) ← decode (h :: (code (s.pc + 2)).toList)
  exec P σ i s

/-- `k` steps from `s`, or `none` when a step stops the model. -/
def run (P : Platform) (σ : Nat → UInt32) (code : UInt32 → Option UInt16) :
    Nat → State → Option State
  | 0, s => some s
  | k + 1, s => (step P σ code s).bind (run P σ code k)

end LeanExe.M7
