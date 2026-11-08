import F7.FPAdd32

/-!
FPSub of Sail's Lean translation of the Armv9.4-A model, at 32 bits under FPCR 0x02000000,
returns Talos's `f32Sub` of its operands for every pair of words and sets in FPSR the bits of
`subMask32`, from every state that satisfies `Hyp`.  Talos's `IEEE32.sub a b` is
`IEEE32.add a (negate b)`, where `negate` flips the sign bit and keeps the exponent and fraction
(`neg_fields32`), so the classification, the sign, and the scaled value of `negate b` follow from
those of `b`.  The proof follows `fpAdd32_run` with the exact difference of two finite operands,
an integer `z` times 2^-149, rounded by `fpRound32_q` and `rsm_eq_rrm32`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem neg_fields32 (y : UInt32) :
    Wasm.IEEE32.exponent (Wasm.IEEE32.negate y) = Wasm.IEEE32.exponent y ∧
      Wasm.IEEE32.fraction (Wasm.IEEE32.negate y) = Wasm.IEEE32.fraction y ∧
      Wasm.IEEE32.sign (Wasm.IEEE32.negate y) = !Wasm.IEEE32.sign y := by
  have hy := y.toNat_lt
  simp only [Wasm.IEEE32.negate, Wasm.IEEE32.encodeFinite, Wasm.IEEE32.exponent,
    Wasm.IEEE32.fraction, Wasm.IEEE32.sign, UInt32.toNat_ofNat']
  by_cases hs : 2 ^ 31 ≤ y.toNat
  · simp only [hs, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    refine ⟨by omega, by omega, ?_⟩
    simp only [decide_eq_false_iff_not, not_le]
    omega
  · simp only [hs, decide_false, Bool.not_false, ite_true]
    refine ⟨by omega, by omega, ?_⟩
    simp only [decide_eq_true_eq]
    omega

theorem neg_isNaN32 (x : BitVec 32) :
    Wasm.IEEE32.isNaN (Wasm.IEEE32.negate (UInt32.ofBitVec x)) = isNaNT (ty32 x) := by
  rw [← t_isNaN32]
  simp only [Wasm.IEEE32.isNaN, (neg_fields32 _).1, (neg_fields32 _).2.1]

theorem neg_isInf32 (x : BitVec 32) :
    Wasm.IEEE32.isInfinite (Wasm.IEEE32.negate (UInt32.ofBitVec x)) =
      (ty32 x == .FPType_Infinity) := by
  rw [← t_isInf32]
  simp only [Wasm.IEEE32.isInfinite, (neg_fields32 _).1, (neg_fields32 _).2.1]

theorem neg_sign32 (x : BitVec 32) :
    Wasm.IEEE32.sign (Wasm.IEEE32.negate (UInt32.ofBitVec x)) = !sg32 x := by
  rw [(neg_fields32 _).2.2, t_sign32]

theorem neg_sv32 (x : BitVec 32) :
    Wasm.IEEE32.scaledValue (Wasm.IEEE32.negate (UInt32.ofBitVec x)) =
      -Wasm.IEEE32.scaledValue (UInt32.ofBitVec x) := by
  obtain ⟨he, hf, hs⟩ := neg_fields32 (UInt32.ofBitVec x)
  simp only [Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude, he, hf, hs]
  cases Wasm.IEEE32.sign (UInt32.ofBitVec x) <;> simp

theorem sum_neg32 (a b : BitVec 32) :
    Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) +
        Wasm.IEEE32.scaledValue (Wasm.IEEE32.negate (UInt32.ofBitVec b)) =
      Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) - Wasm.IEEE32.scaledValue (UInt32.ofBitVec b) := by
  rw [neg_sv32, ← sub_eq_add_neg]

theorem sub_diff32 (A B : ℤ) :
    sub_real ((A : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) ((B : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) =
      ((A - B : ℤ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ) := by
  simp only [sub_real]; push_cast; ring

/-- Two finite operands, not both zeros, whose exact difference is zero are not a negative
minuend and a positive subtrahend. -/
theorem not_neg_pos32 (a b : BitVec 32) (hfa : ex32 a ≠ 255) (hfb : ex32 b ≠ 255)
    (hz : ¬ (ty32 a = .FPType_Zero ∧ ty32 b = .FPType_Zero))
    (hs : Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) -
      Wasm.IEEE32.scaledValue (UInt32.ofBitVec b) = 0) : (sg32 a && !sg32 b) = false := by
  rw [sv32_eq, sv32_eq] at hs
  cases hsa : sg32 a <;> cases hsb : sg32 b <;> simp only [hsa, hsb, ite_true, ite_false,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
    Bool.and_self] at hs ⊢
  exfalso
  have ha0 : Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) = 0 := by omega
  have hb0 : Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec b) = 0 := by omega
  exact hz ⟨(ty32_zero a hfa).mp ha0, (ty32_zero b hfb).mp hb0⟩

/-- The bits of FPSR that FPSub sets at 32 bits under FPCR 0x02000000. -/
def subMask32 (a b : BitVec 32) : BitVec 64 :=
  if isNaNT (ty32 a) || isNaNT (ty32 b) then
    (if ty32 a == .FPType_SNaN || ty32 b == .FPType_SNaN then 1#64 else 0#64)
  else if ty32 a == .FPType_Infinity || ty32 b == .FPType_Infinity then
    (if ty32 a == .FPType_Infinity && ty32 b == .FPType_Infinity && sg32 a != !sg32 b then 1#64
     else 0#64)
  else
    let z := Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) -
      Wasm.IEEE32.scaledValue (UInt32.ofBitVec b)
    if z = 0 then 0#64 else maskQ32 z.natAbs 1

set_option hygiene false in
macro "sub_fin32" : tactic => `(tactic| (
  have hfa : ex32 a ≠ 255 :=
    ty32_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex32 b ≠ 255 :=
    ty32_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hnz : ¬ (ty32 a = .FPType_Zero ∧ ty32 b = .FPType_Zero) := by
    rw [ha, hb]; intro ⟨h1, h2⟩; first | exact FPType.noConfusion h1 | exact FPType.noConfusion h2
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [val32_fin a hfa, val32_fin b hfb, sub_diff32, eq_sum32]
  by_cases hz : Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) -
      Wasm.IEEE32.scaledValue (UInt32.ofBitVec b) = 0
  · have hsg := not_neg_pos32 a b hfa hfb hnz hz
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
    have hz' : (Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) -
        Wasm.IEEE32.scaledValue (UInt32.ofBitVec b) == 0) = false := by simpa using hz
    simp only [hz', Bool.false_eq_true, ↓reduceIte]
    rw [rsm_eq_rrm32 _ _ (Int.natAbs_pos.mpr hz)]
    exact ⟨σ4, rfl, hr4, hf4⟩))

theorem sub_real_zero32 : sub_real 0 0 = 0 := by simp [sub_real]

set_option hygiene false in
macro "sub_sgn32" : tactic => `(tactic| (
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
  all_goals try simp only [hsa, hsb, ↓reduceIte, sub_real_zero32, eq_real_zero32, sub_zero,
    beq_self_eq_true, Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self,
    Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and]
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
theorem fpSub32_run (a b : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPSub a b fpcrV).run s = .ok (Wasm.f32Sub (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| subMask32 a b) ∧ Frame s s' := by
  subst hs
  simp only [FPSub, FPSub__1]
  sail_simp [FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run32 a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run32 b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run32 _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f32Sub, Wasm.IEEE32.sub, Wasm.IEEE32.add, t_isNaN32, t_isInf32, t_sign32,
    neg_isNaN32, neg_isInf32, neg_sign32, sum_neg32, subMask32]
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
  all_goals first | sub_fin32 | skip
  all_goals sub_sgn32

/-- FPSub at 32 bits under FPCR 0x02000000 returns Talos's `f32Sub` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| subMask32 a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpSub32_eq_f32Sub (a b : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPSub a b fpcrV).run s =
        .ok (Wasm.f32Sub (UInt32.ofBitVec a) (UInt32.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| subMask32 a b) ∧ Frame s s' :=
  fpSub32_run a b h rfl

end F7
