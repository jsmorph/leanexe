import F7.Round

/-!
FPAdd of Sail's Lean translation of the Armv9.4-A model, at 64 bits under FPCR 0x02000000,
returns Talos's `f64Add` of its operands for every pair of words and sets in FPSR the bits of
`addMask`, from every state that satisfies `Hyp`.  The proof runs the translated code:
`fpUnpack_run`, `fpProcessNaNs_run` (`F7/Base.lean`), and `fpRound_run` (`F7/Round.lean`) state
what FPUnpack__1, FPProcessNaNs__1, and FPRound__2 return, and `fpAdd_run` puts them together case
by case.  `Frame` states that
memory, tags, cycle count, and output do not change.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}
theorem add_sum (A B : ℤ) :
    add_real ((A : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) ((B : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) =
      ((A + B : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  simp only [add_real]; push_cast; ring

theorem eq_sum (z : ℤ) : eq_real ((z : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) 0 = decide (z = 0) := by
  simp [eq_real]

theorem sop_eq (z : ℤ) (hz : z ≠ 0) :
    (z : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) = sop (decide (z < 0)) z.natAbs 1074 := by
  by_cases hneg : z < 0
  · simp only [sop, hneg, decide_true, if_true]
    rw [Nat.cast_natAbs, abs_of_neg (by exact_mod_cast hneg)]
    push_cast; ring
  · simp only [sop, hneg, decide_false, Bool.false_eq_true, if_false]
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast (not_lt.mp hneg))]

theorem not_both_neg (a b : BitVec 64) (hfa : ex a ≠ 2047) (hfb : ex b ≠ 2047)
    (hz : ¬ (ty64 a = .FPType_Zero ∧ ty64 b = .FPType_Zero))
    (hs : Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = 0) : (sg a && sg b) = false := by
  rw [sv_eq, sv_eq] at hs
  cases hsa : sg a <;> cases hsb : sg b <;> simp only [hsa, hsb, if_true, if_false,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self] at hs ⊢
  exfalso
  have ha0 : Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec a) = 0 := by omega
  have hb0 : Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec b) = 0 := by omega
  exact hz ⟨(ty_zero a hfa).mp ha0, (ty_zero b hfb).mp hb0⟩

/-- The bits of FPSR that FPAdd sets at 64 bits under FPCR 0x02000000. -/
def addMask (a b : BitVec 64) : BitVec 64 :=
  if isNaNT (ty64 a) || isNaNT (ty64 b) then
    (if ty64 a == .FPType_SNaN || ty64 b == .FPType_SNaN then 1#64 else 0#64)
  else if ty64 a == .FPType_Infinity || ty64 b == .FPType_Infinity then
    (if ty64 a == .FPType_Infinity && ty64 b == .FPType_Infinity && sg a != sg b then 1#64
     else 0#64)
  else
    let z := Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b)
    if z = 0 then 0#64 else roundMask z.natAbs

set_option hygiene false in
macro "fin_script" : tactic => `(tactic| (
  have hfa : ex a ≠ 2047 := ty_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex b ≠ 2047 := ty_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hnz : ¬ (ty64 a = .FPType_Zero ∧ ty64 b = .FPType_Zero) := by
    rw [ha, hb]; intro ⟨h1, h2⟩; first | exact FPType.noConfusion h1 | exact FPType.noConfusion h2
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [val_fin a hfa, val_fin b hfb, add_sum, eq_sum]
  by_cases hz : Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = 0
  · have hsg := not_both_neg a b hfa hfb hnz hz
    sail_simp [hz, hsg, FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa]
    refine ⟨_, rfl, ?_, hf3⟩
    rw [hr3', BitVec.or_zero]
    exact (insert_self _ _ _ h.hfpsr).symm
  · rw [sop_eq _ hz]
    sail_simp [hz]
    refine step hf3 (fpRound_run _ _ (Int.natAbs_pos.mpr hz) h hr3') ?_
    intro σ4 hr4 hf4
    sail_simp [FPProcessDenorms, hr4, h.hfi, h.hps, h.nrw, h.aa64, h.fa, Std.ExtDHashMap.get?_insert]
    have hz' : (Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
        Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) == 0) = false := by simpa using hz
    simp only [hz', Bool.false_eq_true, ↓reduceIte, tRound]
    exact ⟨σ4, rfl, hr4, hf4⟩))

theorem add_real_zero : add_real 0 0 = 0 := by simp [add_real]
theorem eq_real_zero : eq_real 0 0 = true := by simp [eq_real]

set_option hygiene false in
macro "sgn_script" : tactic => `(tactic| (
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  cases hsa : sg a <;> cases hsb : sg b <;> (try simp only [sgBit, hsa, hsb, ↓reduceIte] at ⊢)
  all_goals try sail_simp [FPZero, FPInfinity, FPProcessDenorms, FPProcessException, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr]
  all_goals try sail_simp [FPDefaultNaN__1, FPProcessException, FPProcessDenorms, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, setReg_regs, cast_eq, ite_self]
  all_goals try rw [inf_word a (by assumption)]
  all_goals try rw [inf_word b (by assumption)]
  all_goals try rw [val_zero a (by assumption)]
  all_goals try rw [val_zero b (by assumption)]
  all_goals try rw [sv_zero a (by assumption)]
  all_goals try rw [sv_zero b (by assumption)]
  all_goals try simp only [hsa, hsb, ↓reduceIte, add_real_zero, eq_real_zero, add_zero,
    beq_self_eq_true, Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self]
  all_goals try sail_simp [FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa]
  all_goals (
    refine ⟨_, ok_congr ?v, ?r, ⟨hf3.mem, hf3.tags, hf3.cyc, hf3.out⟩⟩
    case v => decide
    case r =>
      first
      | (rw [hr3', BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)
      | (simp only [setReg_regs, bump_regs, faS_regs, hr3', upd_or _ _ (by norm_num : 0 < 64),
          (or_masks _).2.2.1]))))

set_option maxHeartbeats 900000 in
theorem fpAdd_run (a b : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPAdd a b fpcrV).run s = .ok (Wasm.f64Add (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| addMask a b) ∧ Frame s s' := by
  subst hs
  simp only [FPAdd, FPAdd__1]
  sail_simp [FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f64Add, Wasm.IEEE64.add, t_isNaN, t_isInf, t_sign, addMask]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2.1]
  cases ha : ty64 a <;> cases hb : ty64 b <;> simp only [isNaNT] at hr3 ⊢ <;> sail_simp []
  -- The NaN cases.
  all_goals first
    | (refine ⟨σ3, ?_, ?_, hf3⟩
       · rfl
       · rw [hr3]
         simp only [ha, hb, ftb_SNaN_SNaN, ftb_QNaN_SNaN,
           ftb_Zero_SNaN, ftb_Denormal_SNaN,
           ftb_Nonzero_SNaN, ftb_Infinity_SNaN, Bool.or_true,
           Bool.true_or, Bool.or_false, Bool.false_or, ↓reduceIte, Bool.false_eq_true, hioc,
           BitVec.or_zero] <;> first | rfl | exact (insert_self _ _ _ h.hfpsr).symm)
    | skip
  all_goals first | fin_script | skip
  all_goals sgn_script

/-- FPAdd at 64 bits under FPCR 0x02000000 returns Talos's `f64Add` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| addMask a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpAdd_eq_f64Add (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPAdd a b fpcrV).run s =
        .ok (Wasm.f64Add (UInt64.ofBitVec a) (UInt64.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| addMask a b) ∧ Frame s s' :=
  fpAdd_run a b h rfl

end F7
