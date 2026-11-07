import LeanExe.M7.Isla.Check
import LeanExe.M7.Isla.Profile

/-!
Theorems of `Agrees` for the register forms of `LeanExe/M7/Machine.lean`, from the traces of
`tests/isla/m7` under the profile `sys` of `LeanExe/M7/Isla/Profile.lean`.  Each theorem holds for
every register of r0 to r7 in each field, every machine, every platform, and every sequence of
device values.  `tests/isla/m7-theorems.sh` elaborates the module and prints the axioms of its
theorems.

The forward direction of a proof takes each path of the trace to its outcome, and the backward
direction builds the path that keeps bits 63 to 32 of the written register.  `t32_reg_end` and
`t32_reg_bwd` of `LeanExe/M7/Isla/Check.lean` compare the outcome with `exec`'s state, with a
lemma that states the trace's operator on the low words as the model's operator on `UInt32`.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode)

/-- The fields of a form of the three registers `d`, `n`, and `m`. -/
def regFields (d n m : Fin 8) : Fields := [("Rn", n.val), ("Rd", d.val), ("Rm", m.val)]

/-- The footprint of `AND.W Rd, Rn, Rm`. -/
def andRegT : Footprint := isla_trace% "tests/isla/m7/and-reg"

/-- The footprint of `EOR.W Rd, Rn, Rm`. -/
def eorRegT : Footprint := isla_trace% "tests/isla/m7/eor-reg"

/-- The footprint of `ADC.W Rd, Rn, Rm`. -/
def adcRegT : Footprint := isla_trace% "tests/isla/m7/adc-reg"

/-- The footprint of `ORR{S}.W Rd, Rn, Rm`. -/
def orrRegT : Footprint := isla_trace% "tests/isla/m7/orr-reg"

/-- The fields of a form of the three registers `d`, `n`, and `m` with the flag bit `s`. -/
def regFieldsS (s : Fin 2) (d n m : Fin 8) : Fields :=
  [("S", s.val), ("Rn", n.val), ("Rd", d.val), ("Rm", m.val)]

/-- Proves `Agrees` for the footprint `F` of a form that writes one register of r0 to r7 from two
registers and leaves the flags: the decode from the opcode's word, the premise on `σ`, every path
of the trace by `t32_fwd` and `t32_reg_end`, and the path that keeps the high words with the values
`vs` before the reads of `R0` to `R30`, `t32_gprs` of the machine `m`, and `false` for the Boolean
that chooses the write of the register.  `k` is the number of the decode clause, which the trace
writes to `SEE`, and the lemmas in brackets turn the written value into the model's. -/
syntax "reg3_agrees " ident num term:max "[" term,* "]" "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| reg3_agrees $F $k $m [$vs,*] [$xs,*]) => `(tactic| t32_quiet
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, $F:ident, regFields, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [$F:ident, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 $k), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [$F:ident, LeanExe.A64.Isla.Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ]
        all_goals t32_reg_end [$xs,*]
      · unfold footRun
        simp only [$F:ident, LeanExe.A64.Isla.Footprint.vars, regFields, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        t32_bwd [$vs,*] using omega with [hσ]
        t32_gprs $m using omega with [hσ]
        t32_bwd [false] using omega with [hσ]
        all_goals first
          | t32_reg_bwd [$xs,*]
          | t32_side)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `AND.W Rd, Rn, Rm` agrees with `exec` for every register of r0 to r7 in each
field and every machine. -/
theorem andReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n k : Fin 8)
    (m : Mach) : Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"]
      andRegT (regFields d n k) (.andReg d n k) m := by
  reg3_agrees andRegT 2847 m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0]
    [ofNat_and32]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `EOR.W Rd, Rn, Rm` agrees with `exec` for every register of r0 to r7 in each
field and every machine. -/
theorem eorReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n k : Fin 8)
    (m : Mach) : Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"]
      eorRegT (regFields d n k) (.eorReg d n k) m := by
  reg3_agrees eorRegT 2907 m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0]
    [ofNat_xor32]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `ADC.W Rd, Rn, Rm` agrees with `exec` for every register of r0 to r7 in each
field and every machine. -/
theorem adcReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n k : Fin 8)
    (m : Mach) : Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"]
      adcRegT (regFields d n k) (.adcReg d n k) m := by
  reg3_agrees adcRegT 2817 m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0]
    [ofNat_adc32]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `ORR{S}.W Rd, Rn, Rm` agrees with `exec` for both values of the S bit, every
register of r0 to r7 in each field, and every machine.  With S set, the trace forks on a zero
result and writes Z as a constant, so the backward direction takes the cases of S and of a zero
result. -/
theorem orrReg_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (sf : Fin 2)
    (d n k : Fin 8) (m : Mach) : Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"]
      orrRegT (regFieldsS sf d n k) (.orrReg sf d n k) m := by
  t32_quiet
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, orrRegT, regFieldsS, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [orrRegT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 3045), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [orrRegT, LeanExe.A64.Isla.Footprint.vars, regFieldsS, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ]
        all_goals t32_nz_end [← UInt32.toNat_or]
      · unfold footRun
        simp only [orrRegT, LeanExe.A64.Isla.Footprint.vars, regFieldsS, List.foldl, List.lookup,
          String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
          Nat.reduceDiv]
        by_cases hS : sf.val = 1 <;>
          by_cases hz : (m.x n.val % 4294967296 ||| m.x k.val % 4294967296) = 0
        all_goals
          t32_bwd [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, 0] using omega
            with [hσ, hS, hz]
          t32_gprs m using omega with [hσ, hS, hz]
          t32_bwd [false] using omega with [hσ, hS, hz]
        all_goals first
          | t32_nz_bwd [← UInt32.toNat_or]
          | t32_side

#print axioms andReg_agrees
#print axioms adcReg_agrees
#print axioms orrReg_agrees
#print axioms eorReg_agrees

end TestSupport.M7.Isla
