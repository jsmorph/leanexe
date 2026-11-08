import F7.Round32

/-!
FPAdd of Sail's Lean translation of the Armv9.4-A model, at 32 bits under FPCR 0x02000000,
returns Talos's `f32Add` of its operands for every pair of words and sets in FPSR the bits of
`addMask32`, from every state that satisfies `Hyp`.  The proof follows `fpAdd_run` of
`F7/FPAdd.lean` with `fpUnpack_run32`, `fpProcessNaNs_run32`, and `fpRound32_q`
(`F7/Round32.lean`).  The exact sum of two finite operands is an integer `z` times 2^-149, the
rational `|z| / 1` of `fpRound32_q`, and `rsm_eq_rrm32` gives Talos's `roundScaledMagnitude` of
`|z|`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem add_sum32 (A B : ℤ) :
    add_real ((A : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) ((B : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) =
      ((A + B : ℤ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ) := by
  simp only [add_real]; push_cast; ring

theorem eq_sum32 (z : ℤ) : eq_real ((z : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) 0 = decide (z = 0) := by
  simp [eq_real]

/-- A nonzero multiple of 2^-149 as the rational of `fpRound32_q`. -/
theorem qop_int32 (z : ℤ) (hz : z ≠ 0) :
    (z : ℝ) * (2 : ℝ) ^ (-149 : ℤ) = qop (decide (z < 0)) z.natAbs 1 149 := by
  by_cases hneg : z < 0
  · simp only [qop, hneg, decide_true, ite_true, Nat.cast_one, div_one]
    rw [Nat.cast_natAbs, abs_of_neg (by exact_mod_cast hneg)]
    push_cast; ring
  · simp only [qop, hneg, decide_false, Bool.false_eq_true, ite_false, Nat.cast_one, div_one]
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast (not_lt.mp hneg))]

theorem not_both_neg32 (a b : BitVec 32) (hfa : ex32 a ≠ 255) (hfb : ex32 b ≠ 255)
    (hz : ¬ (ty32 a = .FPType_Zero ∧ ty32 b = .FPType_Zero))
    (hs : Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) +
      Wasm.IEEE32.scaledValue (UInt32.ofBitVec b) = 0) : (sg32 a && sg32 b) = false := by
  rw [sv32_eq, sv32_eq] at hs
  cases hsa : sg32 a <;> cases hsb : sg32 b <;> simp only [hsa, hsb, ite_true, ite_false,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self] at hs ⊢
  exfalso
  have ha0 : Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) = 0 := by omega
  have hb0 : Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec b) = 0 := by omega
  exact hz ⟨(ty32_zero a hfa).mp ha0, (ty32_zero b hfb).mp hb0⟩

/-- The bits of FPSR that FPAdd sets at 32 bits under FPCR 0x02000000. -/
def addMask32 (a b : BitVec 32) : BitVec 64 :=
  if isNaNT (ty32 a) || isNaNT (ty32 b) then
    (if ty32 a == .FPType_SNaN || ty32 b == .FPType_SNaN then 1#64 else 0#64)
  else if ty32 a == .FPType_Infinity || ty32 b == .FPType_Infinity then
    (if ty32 a == .FPType_Infinity && ty32 b == .FPType_Infinity && sg32 a != sg32 b then 1#64
     else 0#64)
  else
    let z := Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) +
      Wasm.IEEE32.scaledValue (UInt32.ofBitVec b)
    if z = 0 then 0#64 else maskQ32 z.natAbs 1

set_option hygiene false in
macro "fin_script32" : tactic => `(tactic| (
  have hfa : ex32 a ≠ 255 :=
    ty32_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex32 b ≠ 255 :=
    ty32_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hnz : ¬ (ty32 a = .FPType_Zero ∧ ty32 b = .FPType_Zero) := by
    rw [ha, hb]; intro ⟨h1, h2⟩; first | exact FPType.noConfusion h1 | exact FPType.noConfusion h2
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [val32_fin a hfa, val32_fin b hfb, add_sum32, eq_sum32]
  by_cases hz : Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) +
      Wasm.IEEE32.scaledValue (UInt32.ofBitVec b) = 0
  · have hsg := not_both_neg32 a b hfa hfb hnz hz
    sail_simp [hz, hsg, FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa]
    refine ⟨_, rfl, ?_, hf3⟩
    rw [hr3', BitVec.or_zero]
    exact (insert_self _ _ _ h.hfpsr).symm
  · rw [qop_int32 _ hz]
    sail_simp [hz]
    refine step hf3 (fpRound32_q _ _ _ (Int.natAbs_pos.mpr hz) Nat.one_pos h hr3') ?_
    intro σ4 hr4 hf4
    sail_simp [FPProcessDenorms, hr4, h.hfi, h.hps, h.nrw, h.aa64, h.fa,
      Std.ExtDHashMap.get?_insert]
    have hz' : (Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) +
        Wasm.IEEE32.scaledValue (UInt32.ofBitVec b) == 0) = false := by simpa using hz
    simp only [hz', Bool.false_eq_true, ↓reduceIte]
    rw [rsm_eq_rrm32 _ _ (Int.natAbs_pos.mpr hz)]
    exact ⟨σ4, rfl, hr4, hf4⟩))

theorem add_real_zero32 : add_real 0 0 = 0 := by simp [add_real]
theorem eq_real_zero32 : eq_real 0 0 = true := by simp [eq_real]

set_option hygiene false in
macro "sgn_script32" : tactic => `(tactic| (
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  cases hsa : sg32 a <;> cases hsb : sg32 b <;> (try simp only [sgBit32, hsa, hsb, ↓reduceIte] at ⊢)
  all_goals try sail_simp [FPZero, FPInfinity, FPProcessDenorms, FPProcessException, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr]
  all_goals try sail_simp [FPDefaultNaN__1, FPProcessException, FPProcessDenorms, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, setReg_regs, cast_eq, ite_self]
  all_goals try rw [inf_word32 a (by assumption)]
  all_goals try rw [inf_word32 b (by assumption)]
  all_goals try rw [val32_zero a (by assumption)]
  all_goals try rw [val32_zero b (by assumption)]
  all_goals try rw [sv32_zero a (by assumption)]
  all_goals try rw [sv32_zero b (by assumption)]
  all_goals try simp only [hsa, hsb, ↓reduceIte, add_real_zero32, eq_real_zero32, add_zero,
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
theorem fpAdd32_run (a b : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPAdd a b fpcrV).run s = .ok (Wasm.f32Add (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| addMask32 a b) ∧ Frame s s' := by
  subst hs
  simp only [FPAdd, FPAdd__1]
  sail_simp [FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run32 a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run32 b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run32 _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f32Add, Wasm.IEEE32.add, t_isNaN32, t_isInf32, t_sign32, addMask32]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2.1]
  cases ha : ty32 a <;> cases hb : ty32 b <;> simp only [isNaNT] at hr3 ⊢ <;> sail_simp []
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
  all_goals first | fin_script32 | skip
  all_goals sgn_script32

/-- FPAdd at 32 bits under FPCR 0x02000000 returns Talos's `f32Add` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| addMask32 a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpAdd32_eq_f32Add (a b : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPAdd a b fpcrV).run s =
        .ok (Wasm.f32Add (UInt32.ofBitVec a) (UInt32.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| addMask32 a b) ∧ Frame s s' :=
  fpAdd32_run a b h rfl

end F7
