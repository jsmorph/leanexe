import LeanExe.M7.Encode

/-!
The GNU assembler's syntax for the instructions of the Cortex-M7 model of `LeanExe/M7/Machine.lean`
and the samples of every form that `tests/baremetal/m7-encode.sh` assembles with
`arm-none-eabi-as`.  `asm` writes an instruction with its immediates as numbers and a branch
as a target relative to `.`, the address of the instruction, so the assembler computes each split
field itself.  The samples set each register field to r0 and to r7, each immediate field to 0 and
to its largest value, each shift amount to its smallest and largest values and to 1, every
condition of `B<cond>.W`, and the branch offsets to their limits.
-/

namespace TestSupport.M7

open LeanExe.M7

/-- The name of the register `r` of r0 to r7. -/
def reg (r : Fin 8) : String := s!"r{r.val}"

/-- The suffix of a form that sets the flags when `s` is 1. -/
def sfx (s : Fin 2) : String := if s.val = 1 then "s" else ""

/-- The target of a branch with the byte offset `off` from the instruction's address plus 4,
relative to `.`. -/
def target (off : Int) : String :=
  let k := off + 4
  if k < 0 then s!". - {-k}" else s!". + {k}"

/-- The condition names of `B<cond>.W`, EQ to LE. -/
def condName (c : Fin 14) : String :=
  #["eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le"][c.val]!

/-- The name of the instruction's form, its constructor's. -/
def formName : Instr → String
  | .addReg .. => "addReg" | .adcReg .. => "adcReg" | .subReg .. => "subReg"
  | .sbcReg .. => "sbcReg" | .andReg .. => "andReg" | .orrReg .. => "orrReg"
  | .eorReg .. => "eorReg" | .cmpReg .. => "cmpReg" | .lslReg .. => "lslReg"
  | .lsrReg .. => "lsrReg" | .lslImm .. => "lslImm" | .lsrImm .. => "lsrImm"
  | .subImm .. => "subImm" | .andImm .. => "andImm" | .eorImm .. => "eorImm"
  | .cmpImm .. => "cmpImm" | .movImm .. => "movImm" | .movw .. => "movw" | .movt .. => "movt"
  | .addwSp .. => "addwSp" | .subwSp .. => "subwSp" | .addwSpSp .. => "addwSpSp"
  | .subwSpSp .. => "subwSpSp" | .clz .. => "clz" | .umull .. => "umull" | .mla .. => "mla"
  | .mls .. => "mls" | .udiv .. => "udiv" | .ldr .. => "ldr" | .str .. => "str"
  | .ldrSp .. => "ldrSp" | .strSp .. => "strSp" | .ldrLr .. => "ldrLr" | .strLr .. => "strLr"
  | .bcond .. => "bcond" | .b .. => "b" | .bl .. => "bl" | .bxLr => "bxLr" | .dsb => "dsb"

/-- The instruction in the GNU assembler's unified syntax. -/
def asm : Instr → String
  | .addReg s d n m imm3 imm2 =>
      let k := 4 * imm3.val + imm2.val
      s!"add{sfx s}.w {reg d}, {reg n}, {reg m}" ++ (if k = 0 then "" else s!", lsl #{k}")
  | .adcReg d n m => s!"adc.w {reg d}, {reg n}, {reg m}"
  | .subReg s d n m => s!"sub{sfx s}.w {reg d}, {reg n}, {reg m}"
  | .sbcReg s d n m => s!"sbc{sfx s}.w {reg d}, {reg n}, {reg m}"
  | .andReg d n m => s!"and.w {reg d}, {reg n}, {reg m}"
  | .orrReg s d n m => s!"orr{sfx s}.w {reg d}, {reg n}, {reg m}"
  | .eorReg d n m => s!"eor.w {reg d}, {reg n}, {reg m}"
  | .cmpReg n m => s!"cmp.w {reg n}, {reg m}"
  | .lslReg d n m => s!"lsl.w {reg d}, {reg n}, {reg m}"
  | .lsrReg d n m => s!"lsr.w {reg d}, {reg n}, {reg m}"
  | .lslImm d m imm3 imm2 =>
      let k := 4 * imm3.val + imm2.val
      if k = 0 then s!"mov.w {reg d}, {reg m}" else s!"lsl.w {reg d}, {reg m}, #{k}"
  | .lsrImm d m imm3 imm2 =>
      let k := 4 * imm3.val + imm2.val
      s!"lsr.w {reg d}, {reg m}, #{if k = 0 then 32 else k}"
  | .subImm d n imm => s!"sub.w {reg d}, {reg n}, #{imm.val}"
  | .andImm d n imm => s!"and.w {reg d}, {reg n}, #{imm.val}"
  | .eorImm d n imm => s!"eor.w {reg d}, {reg n}, #{imm.val}"
  | .cmpImm n imm => s!"cmp.w {reg n}, #{imm.val}"
  | .movImm d imm => s!"mov.w {reg d}, #{imm.val}"
  | .movw d imm4 i imm3 imm8 => s!"movw {reg d}, #{(imm16 imm4 i imm3 imm8).toNat}"
  | .movt d imm4 i imm3 imm8 => s!"movt {reg d}, #{(imm16 imm4 i imm3 imm8).toNat}"
  | .addwSp d i imm3 imm8 => s!"addw {reg d}, sp, #{(imm12 i imm3 imm8).toNat}"
  | .subwSp d i imm3 imm8 => s!"subw {reg d}, sp, #{(imm12 i imm3 imm8).toNat}"
  | .addwSpSp i imm3 imm8 => s!"addw sp, sp, #{(imm12 i imm3 imm8).toNat}"
  | .subwSpSp i imm3 imm8 => s!"subw sp, sp, #{(imm12 i imm3 imm8).toNat}"
  | .clz d m => s!"clz {reg d}, {reg m}"
  | .umull lo hi n m _ => s!"umull {reg lo}, {reg hi}, {reg n}, {reg m}"
  | .mla d n m a => s!"mla {reg d}, {reg n}, {reg m}, {reg a}"
  | .mls d n m a => s!"mls {reg d}, {reg n}, {reg m}, {reg a}"
  | .udiv d n m => s!"udiv {reg d}, {reg n}, {reg m}"
  | .ldr t n imm => s!"ldr.w {reg t}, [{reg n}, #{imm.val}]"
  | .str t n imm => s!"str.w {reg t}, [{reg n}, #{imm.val}]"
  | .ldrSp t imm => s!"ldr.w {reg t}, [sp, #{imm.val}]"
  | .strSp t imm => s!"str.w {reg t}, [sp, #{imm.val}]"
  | .ldrLr imm => s!"ldr.w lr, [sp, #{imm.val}]"
  | .strLr imm => s!"str.w lr, [sp, #{imm.val}]"
  | .bcond c s j1 j2 imm6 imm11 =>
      s!"b{condName c}.w {target (sint (bcondOffset s j1 j2 imm6 imm11))}"
  | .b s j1 j2 imm10 imm11 => s!"b.w {target (sint (branchOffset s j1 j2 imm10 imm11))}"
  | .bl s j1 j2 imm10 imm11 => s!"bl {target (sint (branchOffset s j1 j2 imm10 imm11))}"
  | .bxLr => "bx lr"
  | .dsb => "dsb sy"

/-- `UMULL` with the destinations `lo` and `hi`, or with `hi` replaced by the register after `lo`
when the two are equal. -/
def umullOf (lo hi n m : Fin 8) : Instr :=
  if h : lo = hi then
    .umull lo ⟨(lo.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ n m fun e => by
      have := congrArg Fin.val e
      simp only at this
      omega
  else .umull lo hi n m h

/-- The register numbers of the samples: every field r0, every field r7, and two mixtures. -/
def quads : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) :=
  [(0, 0, 0, 0), (7, 7, 7, 7), (1, 2, 3, 4), (6, 5, 4, 3)]

/-- The samples of every form. -/
def samples : List Instr :=
  let regForms := quads.flatMap fun (d, n, m, a) =>
    [.addReg 0 d n m 0 0, .addReg 1 d n m 0 0, Instr.addLsl 0 d n m 1, Instr.addLsl 0 d n m 2,
      Instr.addLsl 1 d n m 31, .adcReg d n m, .subReg 0 d n m, .subReg 1 d n m, .sbcReg 0 d n m,
      .sbcReg 1 d n m, .andReg d n m, .orrReg 0 d n m, .orrReg 1 d n m, .eorReg d n m,
      .cmpReg n m, .lslReg d n m, .lsrReg d n m, Instr.lslBy d m 0, Instr.lslBy d m 1,
      Instr.lslBy d m 31, Instr.lsrBy d m 1, Instr.lsrBy d m 31, Instr.lsrBy d m 32,
      .subImm d n 0, .subImm d n 255, .andImm d n 0, .andImm d n 63, .andImm d n 255,
      .eorImm d n 0, .eorImm d n 1, .eorImm d n 255, .cmpImm n 0, .cmpImm n 255, .movImm d 0,
      .movImm d 255, Instr.movwOf d 0, Instr.movwOf d 65535, Instr.movwOf d 0x1234,
      Instr.movtOf d 0, Instr.movtOf d 65535, Instr.movtOf d 0x8001, Instr.addwSpOf d 0,
      Instr.addwSpOf d 4095, Instr.addwSpOf d 0x9AB, Instr.subwSpOf d 0, Instr.subwSpOf d 4095,
      Instr.subwSpOf d 0x5A5, .clz d m, umullOf d n m a, umullOf n d a m, .mla d n m a,
      .mls d n m a, .udiv d n m, .ldr d n 0, .ldr d n 4095, .ldr d n 0x800, .str d n 0,
      .str d n 4095, .ldrSp d 0, .ldrSp d 4095, .strSp d 0, .strSp d 4092, .strSp d 4095]
  let spForms := [0, 4095, 8, 0x800].flatMap fun v =>
    [Instr.addwSpSpOf v, Instr.subwSpSpOf v, .ldrLr (field 4096 v), .strLr (field 4096 v)]
  let bcondOffsets : List Int := [-1048576, 1048574, 0, -2, 2, 0x55554, -0x2AAAA]
  let condForms := (List.range 14).flatMap fun c =>
    let cond : Fin 14 := ⟨c % 14, Nat.mod_lt _ (by decide)⟩
    bcondOffsets.map fun off => Instr.bcondTo cond off
  let branchOffsets : List Int := [-16777216, 16777214, 0, -2, 4, 0x123456, -0x654322, 0x800000,
    -0x800000, 0x400000, -0x400002]
  let branchForms := branchOffsets.flatMap fun off => [Instr.bTo off, Instr.blTo off]
  regForms ++ spForms ++ condForms ++ branchForms ++ [.bxLr, .dsb]

/-- The assembly file of the samples, one instruction a line. -/
def samplesAsm : String :=
  "\n".intercalate (["  .syntax unified", "  .arch armv7e-m", "  .thumb", "  .text"] ++
    samples.map fun i => s!"  {asm i}") ++ "\n"

/-- The bytes that the encoder gives the samples, each halfword's low byte first. -/
def samplesBytes : ByteArray :=
  ⟨(samples.flatMap fun i =>
    (encode i).flatMap fun (h : UInt16) => [h.toUInt8, (h >>> 8).toUInt8]).toArray⟩

def hex4 (v : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  String.ofList (List.replicate (4 - s.length) '0') ++ s

/-- The differences between the assembler's bytes `bin` and the encoder's for each sample, and the
samples whose halfwords in `bin` do not decode to the sample. -/
def checkBytes (bin : ByteArray) : List String := Id.run do
  let hw (k : Nat) : UInt16 := bin[2 * k]!.toUInt16 ||| bin[2 * k + 1]!.toUInt16 <<< 8
  let mut out := []
  let mut k := 0
  if bin.size ≠ samplesBytes.size then
    out := out ++ [s!"the assembler wrote {bin.size} bytes, the encoder {samplesBytes.size}"]
  for i in samples do
    let e := encode i
    let got := (List.range e.length).map fun j => hw (k + j)
    if got ≠ e then
      out := out ++ [s!"{asm i}: assembler {" ".intercalate (got.map (hex4 ·.toNat))}, encoder " ++
        " ".intercalate (e.map (hex4 ·.toNat))]
    else
      let next := if 2 * (k + e.length) + 1 < bin.size then [hw (k + e.length)] else []
      match decode (got ++ next) with
      | some (j, n) =>
          if encodeNat j ≠ encodeNat i ∨ n ≠ e.length then
            out := out ++ [s!"{asm i}: decoded as {asm j}"]
      | none => out := out ++ [s!"{asm i}: not decoded"]
    k := k + e.length
  return out

end TestSupport.M7
