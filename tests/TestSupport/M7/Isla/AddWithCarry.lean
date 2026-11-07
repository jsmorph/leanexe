import LeanExe.M7.Isla.Arith
import LeanExe.M7.Isla.Profile

/-!
Theorems of `Agrees` for the forms of `LeanExe/M7/Machine.lean` that compute `AddWithCarry`, from
the traces of `tests/isla/m7` under the profile `sys` of `LeanExe/M7/Isla/Profile.lean`: `ADD{S}`
with a shift, `SUB{S}`, `SBC{S}`, `CMP` by a register and by an immediate, `SUB` by an immediate,
and `ADDW` and `SUBW` with SP.  Each theorem holds for every register of r0 to r7 in each field,
every value of the S bit and of the immediate fields, every machine whose program counter plus 4
is below 2^32, every platform, and every sequence of device values.  The theorems of `ADDW` and
`SUBW` with SP as destination also take the premise that the result is a multiple of 4: the
model clears bits 1 and 0 of a value written to SP, as the M-profile does, and the A-profile
writes all 32 bits.  `tests/isla/m7-theorems.sh` elaborates the module and prints the axioms of
its theorems.

The traces compute the sum in 128 bits and write N, Z, C, and V as the bits of a word of 4 bits.
The walk rewrites the trace's overflow test with `awc_v`, `awc_v_c`, or `awc_v_b` of
`LeanExe/M7/Isla/Arith.lean`, and `t32_awc_end` and `t32_awc_bwd` compare the outcome with
`exec`'s state through `awc_eq`, which states the model's `addWithCarry` on natural numbers.  The
traces of `ADDW` and `SUBW` write `SEE` twice, 2823 and 2833 for `ADDW` and 3239 and 3248 for
`SUBW`, so their registers `σ'` set it twice.  They read SP by its name, `R13`, and then read the
register vector with that value of `R13`, so the backward direction of a form with a general
register as destination gives values to the other 30 registers with `t32_gprs13`.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode)

/-- The fields of a form of the three registers `d`, `n`, and `m` with the flag bit `s`. -/
def regFieldsS (s : Fin 2) (d n m : Fin 8) : Fields :=
  [("S", s.val), ("Rn", n.val), ("Rd", d.val), ("Rm", m.val)]

/-- The fields of `ADD{S}.W` with the shift amount `imm3:imm2`. -/
def addFields (s : Fin 2) (d n m : Fin 8) (imm3 : Fin 8) (imm2 : Fin 4) : Fields :=
  [("S", s.val), ("Rn", n.val), ("imm3", imm3.val), ("Rd", d.val), ("imm2", imm2.val),
    ("Rm", m.val)]

/-- The fields of a comparison of the registers `n` and `m`. -/
def cmpFields (n m : Fin 8) : Fields := [("Rn", n.val), ("Rm", m.val)]

/-- The fields of a comparison of the register `n` with an immediate. -/
def cmpImmFields (n : Fin 8) (imm : Fin 256) : Fields := [("Rn", n.val), ("imm8", imm.val)]

/-- The fields of `SUB.W Rd, Rn, #imm`. -/
def subImmFields (d n : Fin 8) (imm : Fin 256) : Fields :=
  [("Rn", n.val), ("Rd", d.val), ("imm8", imm.val)]

/-- The fields of `ADDW` and `SUBW` with SP as source and `d` as destination. -/
def spFields (d : Fin 8) (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256) : Fields :=
  [("i", i.val), ("imm3", imm3.val), ("Rd", d.val), ("imm8", imm8.val)]

/-- The fields of `ADDW` and `SUBW` with SP as source and destination. -/
def spSpFields (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256) : Fields :=
  [("i", i.val), ("imm3", imm3.val), ("imm8", imm8.val)]

/-- The footprint of `ADD{S}.W Rd, Rn, Rm, LSL #k`. -/
def addRegT : Footprint := isla_trace% "tests/isla/m7/add-reg"

/-- The footprint of `SBC{S}.W Rd, Rn, Rm`. -/
def sbcRegT : Footprint := isla_trace% "tests/isla/m7/sbc-reg"

/-- The footprint of `CMP.W Rn, Rm`. -/
def cmpRegT : Footprint := isla_trace% "tests/isla/m7/cmp-reg"

/-- The footprint of `CMP.W Rn, #imm`. -/
def cmpImmT : Footprint := isla_trace% "tests/isla/m7/cmp-imm"

/-- The footprint of `SUB.W Rd, Rn, #imm`. -/
def subImmT : Footprint := isla_trace% "tests/isla/m7/sub-imm"

/-- The footprint of `ADDW Rd, SP, #imm12`. -/
def addwSpT : Footprint := isla_trace% "tests/isla/m7/addw-sp"

/-- The footprint of `SUBW Rd, SP, #imm12`. -/
def subwSpT : Footprint := isla_trace% "tests/isla/m7/subw-sp"

/-- The footprint of `ADDW SP, SP, #imm12`. -/
def addwSpSpT : Footprint := isla_trace% "tests/isla/m7/addw-sp-sp"

/-- The footprint of `SUBW SP, SP, #imm12`. -/
def subwSpSpT : Footprint := isla_trace% "tests/isla/m7/subw-sp-sp"

/-- The footprint of `SUB{S}.W Rd, Rn, Rm`. -/
def subRegT : Footprint := isla_trace% "tests/isla/m7/sub-reg"

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
/-- The trace of `SUB{S}.W Rd, Rn, Rm` agrees with `exec` for both values of the S bit, every
register of r0 to r7 in each field, and every machine whose program counter plus 4 is below
2^32.  The trace forks on the S bit before the decode of the operands, so the backward direction
takes the cases of S. -/
theorem subReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (sf : Fin 2)
    (d n k : Fin 8) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] subRegT (regFieldsS sf d n k)
      (.subReg sf d n k) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, subRegT, regFieldsS, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [subRegT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3243), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [subRegT, LeanExe.A64.Isla.Footprint.vars, regFieldsS, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, awc_v_c]
        all_goals t32_awc_end []
      · unfold footRun
        simp only [subRegT, LeanExe.A64.Isla.Footprint.vars, regFieldsS, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        have hS' : 3770 + sf.val = 3771 ↔ sf.val = 1 := by omega
        by_cases hS : sf.val = 1
        all_goals
          t32_bwd [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0] using omega
            with [hσ, hS', hS, awc_v_c]
          t32_gprs m using omega with [hσ, hS', hS, awc_v_c]
          t32_bwd [false] using omega with [hσ, hS', hS, awc_v_c]
        all_goals first
          | t32_awc_bwd []
          | t32_side'

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
/-- The trace of `ADD{S}.W Rd, Rn, Rm, LSL #(4 * imm3 + imm2)` agrees with `exec` for both values
of the S bit, every register of r0 to r7 in each field, every shift amount, and every machine
whose program counter plus 4 is below 2^32.  The trace forks on a shift amount of 0 and on the
S bit, so the backward direction takes the cases of both. -/
theorem addReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (sf : Fin 2)
    (d n k : Fin 8) (imm3 : Fin 8) (imm2 : Fin 4)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] addRegT
      (addFields sf d n k imm3 imm2) (.addReg sf d n k imm3 imm2) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, addRegT, addFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [addRegT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 2827), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [addRegT, LeanExe.A64.Isla.Footprint.vars, addFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, awc_v, imm5_mod64, imm5_div63, imm5_mod32, imm5_lt32,
          sint_imm5, sint_zero, sint_32]
        all_goals t32_awc_end []
      · unfold footRun
        simp only [addRegT, LeanExe.A64.Isla.Footprint.vars, addFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases hc : imm3.val * 4 + imm2.val = 0 <;> by_cases hS : sf.val = 1
        all_goals
          t32_bwd [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0] using omega
            with [hσ, hc, hS, awc_v, imm5_mod64, imm5_div63, imm5_mod32, imm5_lt32, sint_imm5,
              sint_zero, sint_32]
          t32_gprs m using omega with [hσ, hc, hS, awc_v, imm5_mod64, imm5_div63, imm5_mod32,
            imm5_lt32, sint_imm5, sint_zero, sint_32]
          t32_bwd [false] using omega with [hσ, hc, hS, awc_v, imm5_mod64, imm5_div63, imm5_mod32,
            imm5_lt32, sint_imm5, sint_zero, sint_32]
        all_goals first
          | t32_awc_bwd []
          | t32_side'

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
/-- The trace of `SBC{S}.W Rd, Rn, Rm` agrees with `exec` for both values of the S bit, every
register of r0 to r7 in each field, and every machine whose program counter plus 4 is below
2^32. -/
theorem sbcReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (sf : Fin 2)
    (d n k : Fin 8) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] sbcRegT (regFieldsS sf d n k)
      (.sbcReg sf d n k) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, sbcRegT, regFieldsS, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [sbcRegT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3117), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [sbcRegT, LeanExe.A64.Isla.Footprint.vars, regFieldsS, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, awc_v_b]
        all_goals t32_awc_end []
      · unfold footRun
        simp only [sbcRegT, LeanExe.A64.Isla.Footprint.vars, regFieldsS, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases hS : sf.val = 1
        all_goals
          t32_bwd [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0] using omega
            with [hσ, hS, awc_v_b]
          t32_gprs m using omega with [hσ, hS, awc_v_b]
          t32_bwd [false] using omega with [hσ, hS, awc_v_b]
        all_goals first
          | t32_awc_bwd []
          | t32_side'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `CMP.W Rn, Rm` agrees with `exec` for every register of r0 to r7 in each field and
every machine whose program counter plus 4 is below 2^32. -/
theorem cmpReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (n k : Fin 8)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] cmpRegT (cmpFields n k)
      (.cmpReg n k) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, cmpRegT, cmpFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [cmpRegT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 2895), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [cmpRegT, LeanExe.A64.Isla.Footprint.vars, cmpFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, awc_v_c]
        all_goals t32_awc_end []
      · unfold footRun
        simp only [cmpRegT, LeanExe.A64.Isla.Footprint.vars, cmpFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        t32_bwd [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0] using omega
          with [hσ, awc_v_c]
        t32_gprs m using omega with [hσ, awc_v_c]
        all_goals first
          | t32_awc_bwd []
          | t32_side'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `CMP.W Rn, #imm` agrees with `exec` for every register of r0 to r7, every
immediate of 8 bits, and every machine whose program counter plus 4 is below 2^32. -/
theorem cmpImm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (n : Fin 8) (imm : Fin 256)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] cmpImmT (cmpImmFields n imm)
      (.cmpImm n imm) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, cmpImmT, cmpImmFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [cmpImmT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 2891), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [cmpImmT, LeanExe.A64.Isla.Footprint.vars, cmpImmFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, awc_v_c]
        all_goals t32_awc_end []
      · unfold footRun
        simp only [cmpImmT, LeanExe.A64.Isla.Footprint.vars, cmpImmFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        t32_bwd [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat] using omega
          with [hσ, awc_v_c]
        t32_gprs m using omega with [hσ, awc_v_c]
        all_goals first
          | t32_awc_bwd []
          | t32_side'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `SUB.W Rd, Rn, #imm` agrees with `exec` for every register of r0 to r7 in each
field, every immediate of 8 bits, and every machine whose program counter plus 4 is below
2^32. -/
theorem subImm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n : Fin 8)
    (imm : Fin 256) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] subImmT (subImmFields d n imm)
      (.subImm d n imm) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, subImmT, subImmFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [subImmT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3238), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [subImmT, LeanExe.A64.Isla.Footprint.vars, subImmFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ]
        all_goals t32_awc_end []
      · unfold footRun
        simp only [subImmT, LeanExe.A64.Isla.Footprint.vars, subImmFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        t32_bwd [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat] using omega with [hσ]
        t32_gprs m using omega with [hσ]
        t32_bwd [false] using omega with [hσ]
        all_goals first
          | t32_awc_bwd []
          | t32_side'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `ADDW Rd, SP, #imm12` agrees with `exec` for every register of r0 to r7, every
immediate of 12 bits, and every machine whose program counter plus 4 is below 2^32.  The trace
reads SP by its name, `R13`, and the model reads all 32 bits of SP, as the A-profile does. -/
theorem addwSp_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d : Fin 8) (i : Fin 2)
    (imm3 : Fin 8) (imm8 : Fin 256)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] addwSpT (spFields d i imm3 imm8)
      (.addwSp d i imm3 imm8) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, addwSpT, spFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [addwSpT, sys_get, sys] at hσ
      refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 2823)).set "SEE" (.bits 128 2833), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [addwSpT, LeanExe.A64.Isla.Footprint.vars, spFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ]
        all_goals t32_awc_end []
      · unfold footRun
        simp only [addwSpT, LeanExe.A64.Isla.Footprint.vars, spFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        t32_bwd [u.feature, m.s.pc.toNat, Mach.x m 13, false] using omega with [hσ]
        t32_gprs13 m using omega with [hσ]
        all_goals first
          | t32_awc_bwd []
          | t32_side'

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8000 in
/-- The trace of `SUBW Rd, SP, #imm12` agrees with `exec` for every register of r0 to r7, every
immediate of 12 bits, and every machine whose program counter plus 4 is below 2^32. -/
theorem subwSp_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d : Fin 8) (i : Fin 2)
    (imm3 : Fin 8) (imm8 : Fin 256)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] subwSpT (spFields d i imm3 imm8)
      (.subwSp d i imm3 imm8) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, subwSpT, spFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [subwSpT, sys_get, sys] at hσ
      refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3239)).set "SEE" (.bits 128 3248), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [subwSpT, LeanExe.A64.Isla.Footprint.vars, spFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ]
        all_goals t32_awc_end []
      · unfold footRun
        simp only [subwSpT, LeanExe.A64.Isla.Footprint.vars, spFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        t32_bwd [u.feature, m.s.pc.toNat, Mach.x m 13, false] using omega with [hσ]
        t32_gprs13 m using omega with [hσ]
        all_goals first
          | t32_awc_bwd []
          | t32_side'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `ADDW SP, SP, #imm12` agrees with `exec` for every immediate of 12 bits and every
machine whose program counter plus 4 is below 2^32 and whose sum is a multiple of 4.  The
model clears bits 1 and 0 of a value written to SP, as the M-profile does, and the A-profile
writes all 32 bits, so the two agree only on such sums. -/
theorem addwSpSp_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (i : Fin 2)
    (imm3 : Fin 8) (imm8 : Fin 256)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (hsp : (m.s.sp + imm12 i imm3 imm8) % 4 = 0) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] addwSpSpT (spSpFields i imm3 imm8)
      (.addwSpSp i imm3 imm8) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, addwSpSpT, spSpFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [addwSpSpT, sys_get, sys] at hσ
      refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 2823)).set "SEE" (.bits 128 2833), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [addwSpSpT, LeanExe.A64.Isla.Footprint.vars, spSpFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ]
        all_goals t32_awc_end [add_addWithCarry, and_fffffffc hsp]
      · unfold footRun
        simp only [addwSpSpT, LeanExe.A64.Isla.Footprint.vars, spSpFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        t32_bwd [u.feature, m.s.pc.toNat, Mach.x m 13, false] using omega with [hσ]
        all_goals first
          | t32_awc_bwd [add_addWithCarry, and_fffffffc hsp]
          | t32_side'

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8000 in
/-- The trace of `SUBW SP, SP, #imm12` agrees with `exec` for every immediate of 12 bits and every
machine whose program counter plus 4 is below 2^32 and whose difference is a multiple of 4, as
for `ADDW SP, SP, #imm12`. -/
theorem subwSpSp_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (i : Fin 2)
    (imm3 : Fin 8) (imm8 : Fin 256)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (hsp : (m.s.sp - imm12 i imm3 imm8) % 4 = 0) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] subwSpSpT (spSpFields i imm3 imm8)
      (.subwSpSp i imm3 imm8) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, subwSpSpT, spSpFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [subwSpSpT, sys_get, sys] at hσ
      refine ⟨(((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3239)).set "SEE" (.bits 128 3248), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [subwSpSpT, LeanExe.A64.Isla.Footprint.vars, spSpFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ]
        all_goals t32_awc_end [sub_addWithCarry, and_fffffffc hsp]
      · unfold footRun
        simp only [subwSpSpT, LeanExe.A64.Isla.Footprint.vars, spSpFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        t32_bwd [u.feature, m.s.pc.toNat, Mach.x m 13, false] using omega with [hσ]
        all_goals first
          | t32_awc_bwd [sub_addWithCarry, and_fffffffc hsp]
          | t32_side'

#print axioms subReg_agrees
#print axioms addReg_agrees
#print axioms sbcReg_agrees
#print axioms cmpReg_agrees
#print axioms cmpImm_agrees
#print axioms subImm_agrees
#print axioms addwSp_agrees
#print axioms subwSp_agrees
#print axioms addwSpSp_agrees
#print axioms subwSpSp_agrees

end TestSupport.M7.Isla
