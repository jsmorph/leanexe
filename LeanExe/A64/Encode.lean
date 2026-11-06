import LeanExe.A64.Machine

/-!
The encoder of the model's instruction forms and the lemma `decode_encode`: the decoder reads
every encoded instruction back as itself.  Each encoding is the form's fixed bits plus its fields
at their positions, written as a sum of natural numbers, so the proof reads each field back with
`omega` and uses no bit-vector decision procedure.  GNU `as` assembles sample instructions of
every form to the same words.
-/

namespace LeanExe.A64

/-- The value of the 32-bit word of the instruction `i`. -/
def encodeNat : Instr → Nat
  | .movz d imm hw => 0xD2800000 + hw.val * 2097152 + imm.val * 32 + d.val
  | .movk d imm hw => 0xF2800000 + hw.val * 2097152 + imm.val * 32 + d.val
  | .addImm d n imm => 0x91000000 + imm.val * 1024 + n.val * 32 + d.val
  | .subImm d n imm => 0xD1000000 + imm.val * 1024 + n.val * 32 + d.val
  | .subsImm d n imm => 0xF1000000 + imm.val * 1024 + n.val * 32 + d.val
  | .subsReg d n m => 0xEB000000 + m.val * 65536 + n.val * 32 + d.val
  | .csinc d n m cond =>
      0x9A800400 + m.val * 65536 + cond.val * 4096 + n.val * 32 + d.val
  | .orrReg d n m => 0xAA000000 + m.val * 65536 + n.val * 32 + d.val
  | .lsrImm d n sh => 0xD340FC00 + sh.val * 65536 + n.val * 32 + d.val
  | .ldr t n imm => 0xF9400000 + imm.val * 1024 + n.val * 32 + t.val
  | .str t n imm => 0xF9000000 + imm.val * 1024 + n.val * 32 + t.val
  | .strb t n imm => 0x39000000 + imm.val * 1024 + n.val * 32 + t.val
  | .b imm => 0x14000000 + imm.val
  | .bl imm => 0x94000000 + imm.val
  | .cbz t imm => 0xB4000000 + imm.val * 32 + t.val
  | .cbnz t imm => 0xB5000000 + imm.val * 32 + t.val
  | .ret n => 0xD65F0000 + n.val * 32
  | .udiv d n m => 0x9AC00800 + m.val * 65536 + n.val * 32 + d.val
  | .msub d n m a =>
      0x9B008000 + m.val * 65536 + a.val * 1024 + n.val * 32 + d.val
  | .addReg d n m => 0x8B000000 + m.val * 65536 + n.val * 32 + d.val
  | .subReg d n m => 0xCB000000 + m.val * 65536 + n.val * 32 + d.val
  | .andReg d n m => 0x8A000000 + m.val * 65536 + n.val * 32 + d.val
  | .eorReg d n m => 0xCA000000 + m.val * 65536 + n.val * 32 + d.val
  | .madd d n m a => 0x9B000000 + m.val * 65536 + a.val * 1024 + n.val * 32 + d.val
  | .lslv d n m => 0x9AC02000 + m.val * 65536 + n.val * 32 + d.val
  | .lsrv d n m => 0x9AC02400 + m.val * 65536 + n.val * 32 + d.val
  | .orrW d n m => 0x2A000000 + m.val * 65536 + n.val * 32 + d.val
  | .bcond cond imm => 0x54000000 + imm.val * 32 + cond.val
  | .fmovDX d n => 0x9E670000 + n.val * 32 + d.val
  | .fmovXD d n => 0x9E660000 + n.val * 32 + d.val
  | .fadd d n m => 0x1E602800 + m.val * 65536 + n.val * 32 + d.val
  | .fsub d n m => 0x1E603800 + m.val * 65536 + n.val * 32 + d.val
  | .fmul d n m => 0x1E600800 + m.val * 65536 + n.val * 32 + d.val
  | .fdiv d n m => 0x1E601800 + m.val * 65536 + n.val * 32 + d.val
  | .fsqrt d n => 0x1E61C000 + n.val * 32 + d.val
  | .fabs d n => 0x1E60C000 + n.val * 32 + d.val
  | .ucvtf d n => 0x9E630000 + n.val * 32 + d.val

/-- The 32-bit word of the instruction `i`. -/
def encode (i : Instr) : UInt32 :=
  .ofNat (encodeNat i)

theorem encodeNat_lt (i : Instr) : encodeNat i < 4294967296 := by
  cases i <;> simp only [encodeNat] <;> omega

theorem toNat_encode (i : Instr) : (encode i).toNat = encodeNat i := by
  rw [encode]
  exact UInt32.toNat_ofNat_of_lt' (encodeNat_lt i)

/-- Proves `decodeNat v = some i` for one form `i`, with a hypothesis that `encodeNat i = v` in
context: it unfolds that hypothesis and the decoder, takes each condition of the decoder in turn
to be true or false with `omega`, which knows the bounds of `Fin` fields, until it reaches the
form's own branch, and reads the fields back with `omega`. -/
syntax "decode_encode_tac" : tactic
macro_rules
  | `(tactic| decode_encode_tac) => `(tactic| (
      simp only [encodeNat] at *
      dsimp only [decodeNat]
      repeat (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)])
      simp only [Option.some.injEq, Instr.movz.injEq, Instr.movk.injEq, Instr.addImm.injEq,
        Instr.subImm.injEq, Instr.subsImm.injEq, Instr.subsReg.injEq, Instr.csinc.injEq,
        Instr.orrReg.injEq, Instr.lsrImm.injEq,
        Instr.ldr.injEq, Instr.str.injEq, Instr.strb.injEq, Instr.b.injEq, Instr.bl.injEq,
        Instr.cbz.injEq, Instr.cbnz.injEq, Instr.ret.injEq, Instr.udiv.injEq, Instr.msub.injEq,
        Instr.addReg.injEq, Instr.subReg.injEq, Instr.andReg.injEq, Instr.eorReg.injEq,
        Instr.madd.injEq, Instr.lslv.injEq, Instr.lsrv.injEq, Instr.orrW.injEq,
        Instr.bcond.injEq, Instr.fmovDX.injEq, Instr.fmovXD.injEq, Instr.fadd.injEq,
        Instr.fsub.injEq, Instr.fmul.injEq, Instr.fdiv.injEq, Instr.fsqrt.injEq, Instr.fabs.injEq,
        Instr.ucvtf.injEq, Fin.ext_iff]
      omega))

set_option maxHeartbeats 1000000 in
/-- The decoder reads every encoded form back as itself.  Each form's case decides every earlier
condition of the decoder's chain with `omega`, so the proof's cost grows with the product of the
number of forms and the chain's length, beyond the default budget of heartbeats. -/
theorem decode_encode (i : Instr) : decode (encode i) = some i := by
  rw [decode, toNat_encode]
  generalize hv : encodeNat i = v
  cases i <;> decode_encode_tac

end LeanExe.A64
