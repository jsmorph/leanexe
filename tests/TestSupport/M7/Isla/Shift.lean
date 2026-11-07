import LeanExe.M7.Isla.Arith
import LeanExe.M7.Isla.Profile

/-!
Theorems of `Agrees` for the shifts of `LeanExe/M7/Machine.lean`, `LSL.W` and `LSR.W` by a
register and by an immediate, from the traces of `tests/isla/m7` under the profile `sys` of
`LeanExe/M7/Isla/Profile.lean`.  Each theorem holds for every register of r0 to r7 in each field,
every shift amount, every machine whose program counter plus 4 is below 2^32, every platform, and
every sequence of device values.  `tests/isla/m7-theorems.sh` elaborates the module and prints the
axioms of its theorems.

A trace tests the shift amount before it shifts: the shifts by a register fork on an amount of 0,
from 1 to 32, and above 32, and the shifts by an immediate on an amount of 0.  The walk drops the
sign extension of the amount with the lemmas of `LeanExe/M7/Isla/Arith.lean`, the backward
direction takes the cases of the tests, and `ofNat_shl` and `ofNat_shr` state the trace's
`bvshl` and `bvlshr` as the model's `shl` and `shr`.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode)

/-- The fields of a form of the three registers `d`, `n`, and `m`. -/
def regFields (d n m : Fin 8) : Fields := [("Rn", n.val), ("Rd", d.val), ("Rm", m.val)]

/-- The fields of a shift of the register `m` into `d` by `imm3:imm2`. -/
def immFields (d m : Fin 8) (imm3 : Fin 8) (imm2 : Fin 4) : Fields :=
  [("imm3", imm3.val), ("Rd", d.val), ("imm2", imm2.val), ("Rm", m.val)]

/-- The footprint of `LSL.W Rd, Rn, Rm`. -/
def lslRegT : Footprint := isla_trace% "tests/isla/m7/lsl-reg"

/-- The footprint of `LSR.W Rd, Rn, Rm`. -/
def lsrRegT : Footprint := isla_trace% "tests/isla/m7/lsr-reg"

/-- The footprint of `LSL.W Rd, Rm, #imm`. -/
def lslImmT : Footprint := isla_trace% "tests/isla/m7/lsl-imm"

/-- The footprint of `LSR.W Rd, Rm, #imm`. -/
def lsrImmT : Footprint := isla_trace% "tests/isla/m7/lsr-imm"

/-- Builds the path of a shift's trace that keeps the high words, with the values `vs` before the
reads of `R0` to `R30`, `t32_gprs` of the machine `m`, and `false` for the Boolean that chooses the
write of the register, and with the facts in brackets that decide the trace's tests. -/
syntax "shift_bwd " term:max "[" term,* "]" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| shift_bwd $m [$vs,*] [$xs,*]) => `(tactic| (
    t32_bwd [$vs,*] using omega with [$xs,*, mod256_mod64, mod256_div63, mod256_mod32,
      sint_mod256, sint_zero, sint_32, imm5_mod64, imm5_div63, imm5_mod32, imm5_lt32, sint_imm5]
    t32_gprs $m using omega with [$xs,*, mod256_mod64, mod256_div63, mod256_mod32,
      sint_mod256, sint_zero, sint_32, imm5_mod64, imm5_div63, imm5_mod32, imm5_lt32, sint_imm5]
    t32_bwd [false] using omega with [$xs,*, mod256_mod64, mod256_div63, mod256_mod32,
      sint_mod256, sint_zero, sint_32, imm5_mod64, imm5_div63, imm5_mod32, imm5_lt32, sint_imm5]))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `LSL.W Rd, Rn, Rm` agrees with `exec` for every register of r0 to r7 in each
field and every machine whose program counter plus 4 is below 2^32. -/
theorem lslReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n k : Fin 8)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] lslRegT (regFields d n k)
      (.lslReg d n k) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, lslRegT, regFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [lslRegT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 2998), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [lslRegT, LeanExe.A64.Isla.Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, mod256_mod64, mod256_div63, mod256_mod32, sint_mod256,
          sint_zero, sint_32]
        all_goals t32_val_end [ofNat_shl, shl_zero]
      · unfold footRun
        simp only [lslRegT, LeanExe.A64.Isla.Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases hc : m.x k.val % 4294967296 % 256 = 0
        · shift_bwd m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat] [hσ, hc]
          all_goals first
            | t32_side'
            | t32_val_bwd [ofNat_shl, shl_zero]
        · by_cases hd : ((m.x k.val % 4294967296 % 256 : Nat) : Int) ≤ 32
          all_goals
            shift_bwd m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat] [hσ, hc, hd]
          all_goals first
            | t32_side'
            | t32_val_bwd [ofNat_shl, shl_zero]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `LSR.W Rd, Rn, Rm` agrees with `exec` for every register of r0 to r7 in each
field and every machine whose program counter plus 4 is below 2^32. -/
theorem lsrReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n k : Fin 8)
    (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] lsrRegT (regFields d n k)
      (.lsrReg d n k) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, lsrRegT, regFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [lsrRegT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3020), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [lsrRegT, LeanExe.A64.Isla.Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, mod256_mod64, mod256_div63, mod256_mod32, sint_mod256,
          sint_zero, sint_32]
        all_goals t32_val_end [ofNat_shr, shr_zero]
      · unfold footRun
        simp only [lsrRegT, LeanExe.A64.Isla.Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases hc : m.x k.val % 4294967296 % 256 = 0
        · shift_bwd m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat] [hσ, hc]
          all_goals first
            | t32_side'
            | t32_val_bwd [ofNat_shr, shr_zero]
        · by_cases hd : ((m.x k.val % 4294967296 % 256 : Nat) : Int) ≤ 32
          all_goals
            shift_bwd m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat] [hσ, hc, hd]
          all_goals first
            | t32_side'
            | t32_val_bwd [ofNat_shr, shr_zero]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The trace of `LSL.W Rd, Rm, #imm` agrees with `exec` for every register of r0 to r7 in each
field, every shift amount `imm3:imm2`, and every machine whose program counter plus 4 is below
2^32. -/
theorem lslImm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d k : Fin 8)
    (imm3 : Fin 8) (imm2 : Fin 4) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] lslImmT
      (immFields d k imm3 imm2) (.lslImm d k imm3 imm2) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, lslImmT, immFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [lslImmT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3017), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [lslImmT, LeanExe.A64.Isla.Footprint.vars, immFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, imm5_mod64, imm5_div63, imm5_mod32, imm5_lt32, sint_imm5,
          sint_zero, sint_32]
        all_goals t32_val_end [ofNat_shl, ofNat_shl_lt, shl_zero, four_mul]
      · unfold footRun
        simp only [lslImmT, LeanExe.A64.Isla.Footprint.vars, immFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases hc : imm3.val * 4 + imm2.val = 0
        all_goals
          shift_bwd m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0] [hσ, hc]
        all_goals first
          | t32_side'
          | t32_val_bwd [ofNat_shl, ofNat_shl_lt, shl_zero, four_mul]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The trace of `LSR.W Rd, Rm, #imm` agrees with `exec` for every register of r0 to r7 in each
field, every shift amount `imm3:imm2`, of which 0 encodes 32, and every machine whose program
counter plus 4 is below 2^32. -/
theorem lsrImm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d k : Fin 8)
    (imm3 : Fin 8) (imm2 : Fin 4) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] lsrImmT
      (immFields d k imm3 imm2) (.lsrImm d k imm3 imm2) m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, lsrImmT, immFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [lsrImmT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3017), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [lsrImmT, LeanExe.A64.Isla.Footprint.vars, immFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ, imm5_mod64, imm5_div63, imm5_mod32, imm5_lt32, sint_imm5,
          sint_zero, sint_32]
        all_goals t32_val_end [ofNat_shr, ofNat_shr_lt, shr_32, four_mul]
      · unfold footRun
        simp only [lsrImmT, LeanExe.A64.Isla.Footprint.vars, immFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases hc : imm3.val * 4 + imm2.val = 0
        all_goals simp only [four_mul, hc, eq_self_iff_true, ↓reduceIte, shr_32]
        all_goals
          shift_bwd m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0] [hσ, hc]
        all_goals first
          | t32_side'
          | t32_val_bwd [ofNat_shr, ofNat_shr_lt, shr_32, four_mul]

#print axioms lslReg_agrees
#print axioms lsrReg_agrees
#print axioms lslImm_agrees
#print axioms lsrImm_agrees

end TestSupport.M7.Isla
