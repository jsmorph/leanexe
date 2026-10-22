import Library.Numerics.Float64.Erf.ErfNegative

/-!
One step for `Erf.erfWith Exp.expTable x` for every finite `x`.  For a clear sign bit it is
`ErfPositive.erf_pos`.  For a set sign bit, `erf_neg_bits` shows that the result is the negation of
the result at `-x`, branch by branch, with the lemmas of `ErfNegative`, and `erf (-x) = -erf x`
with `F64SignedRounding.within_negate` carries the step.
-/

namespace Library.Numerics.Float64.Erf.ErfOdd
open CodeLib.IEEE64 LeanExe.ProofKit F64Horner RealErf ErfSmallBase ErfMiddleBase ErfTailSplit
  ErfTailEval ErfEnds ErfSub ErfBits ErfPositive ErfNegative F64NegateOps

set_option exponentiation.threshold 4096

/-- `erf p` lies in `[2^-1073, 2]` for `p ≥ 2^-28`. -/
theorem erf_range (p : ℝ) (hp : 1 / 2 ^ 28 ≤ p) : 2 / 2 ^ 1074 ≤ RealErf.erf p ∧ RealErf.erf p ≤ 2 := by
  constructor
  · have hm := erf_strictMono.monotone hp
    have hl := ErfSmallBase.erf_lower (1 / 2 ^ 28) (by positivity)
    have hk := scale_bounds.1
    have h1 : (2 : ℝ) / 2 ^ 1074 ≤ 333038747416263463341 / 2 ^ 68 *
        (1 / 2 ^ 28 * (1 - (1 / 2 ^ 28) ^ 2 / 3)) := by norm_num
    have h2 : (333038747416263463341 / 2 ^ 68 : ℝ) * (1 / 2 ^ 28 * (1 - (1 / 2 ^ 28) ^ 2 / 3)) ≤
        scale * (1 / 2 ^ 28 * (1 - (1 / 2 ^ 28) ^ 2 / 3)) :=
      mul_le_mul_of_nonneg_right hk (by norm_num)
    linarith
  · have := erf_lt_one p
    linarith

theorem float_abs_eq (x : Float) (hxf : Finite x.toBits) : (-x).abs = x.abs := by
  rw [← F64Bits.ofBits_toBits (-x).abs, ← F64Bits.ofBits_toBits x.abs, F64Bits.toBits_abs,
    F64Bits.toBits_abs, neg_toBits x hxf, abs_negate]

theorem neg_ofBits (w : UInt64) (hw : Wasm.IEEE64.isNaN w = false) :
    (-Float.ofBits w).toBits = Wasm.IEEE64.negate w := by
  rw [F64Bits.toBits_neg, F64Bits.toBits_ofBits, F64Sign.sub_negZero]
  simp [hw]

/-- The result at a negative argument is the negation of the result at its magnitude. -/
theorem erf_neg_bits (x : Float) (hxf : Finite x.toBits) (hs : Wasm.IEEE64.sign x.toBits = true) :
    (Erf.erfWith Exp.expTable x).toBits =
      Wasm.IEEE64.negate (Erf.erfWith Exp.expTable (-x)).toBits := by
  have hnx : (-x).toBits = Wasm.IEEE64.negate x.toBits := neg_toBits x hxf
  have hPf : Finite (-x).toBits := by rw [hnx]; exact finite_negate _ hxf
  have hPs : Wasm.IEEE64.sign (-x).toBits = false := by
    rw [hnx, (F64Sign.fields_negate _).2.2, hs]
    rfl
  have hbn : x.toBits = Wasm.IEEE64.negate (-x).toBits := by
    rw [hnx, F64RelativeStep.negate_negate]
  have hpos := erf_pos (-x) hPf hPs
  have hv0 : 0 ≤ value (-x).toBits := by
    simp only [value, Wasm.IEEE64.scaledValue, hPs, Bool.false_eq_true, ↓reduceIte]
    positivity
  have hix : (((-x).toBits >>> 32) &&& (0x7fffffff : UInt64)) =
      ((x.toBits >>> 32) &&& (0x7fffffff : UInt64)) := by
    rw [hnx, ix_negate]
  have hneg : (x.toBits >>> 32 >>> 31 == 1) = true := by rw [neg_flag]; exact hs
  have hneg' : ((-x).toBits >>> 32 >>> 31 == 1) = false := by rw [neg_flag]; exact hPs
  have habs := float_abs_eq x hxf
  have hxa : (-x).abs.toBits = (-x).toBits := by rw [F64Bits.toBits_abs, abs_eq_self _ hPs]
  obtain ⟨_, hsm, htiny, hsub, hmid, hsix, _⟩ := ix_conds (-x) hPf
  rw [abs_of_nonneg hv0, hix] at hsm htiny hsub hmid hsix
  rw [sel_inf_free _ x hxf]
  rw [sel_inf_free _ (-x) hPf, hix, hneg'] at hpos ⊢
  rw [hneg, ← habs]
  simp only [Bool.false_eq_true, ↓reduceIte] at hpos ⊢
  have n8 : Wasm.IEEE64.isNaN 0x3FF06EBA8214DB69 = false := by decide
  have n1 : Wasm.IEEE64.isNaN 0x3FC06EBA8214DB69 = false := by decide
  have ne : Wasm.IEEE64.isNaN 0x3FEB0AC160000000 = false := by decide
  have nt : Wasm.IEEE64.isNaN 0x01A56E1FC2F8F359 = false := by decide
  have hef : Finite (0x3FEB0AC160000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  by_cases h1 : value (-x).toBits < 27 / 32
  · simp only [hsm.mpr h1, ↓reduceIte] at hpos ⊢
    by_cases h2 : value (-x).toBits < 1 / 2 ^ 28
    · simp only [htiny.mpr h2, ↓reduceIte] at hpos ⊢
      by_cases h3 : value (-x).toBits < 1 / 2 ^ 1015
      · simp only [hsub.mpr h3, ↓reduceIte] at hpos ⊢
        simp only [F64Bits.toBits_div, F64Bits.toBits_add, F64Bits.toBits_mul,
          F64Bits.toBits_ofBits, n8, eight_bits, Bool.false_eq_true, ↓reduceIte]
        rw [hbn]
        rcases eq_or_lt_of_le hv0 with h0 | h0
        · rw [eq_zero_of_value (-x).toBits hPs h0.symm]
          decide +kernel
        · exact sub_negate (-x).toBits hPf h0 (h3.le.trans (by norm_num))
      · simp only [show ¬ _ from fun h => h3 (hsub.mp h), ↓reduceIte] at hpos ⊢
        simp only [F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits, n1,
          Bool.false_eq_true, ↓reduceIte]
        rw [hbn]
        have h0 : 0 < value (-x).toBits := lt_of_lt_of_le (by positivity) (not_lt.mp h3)
        exact tiny_negate (-x).toBits hPf h0 (h2.le.trans (by norm_num))
    · simp only [show ¬ _ from fun h => h2 (htiny.mp h), ↓reduceIte] at hpos ⊢
      simp only [F64Bits.toBits_add, F64Bits.toBits_mul, erfSmall_bits] at hpos ⊢
      rw [hbn, mul_negate_self (-x).toBits hPf]
      obtain ⟨hy1, hy2⟩ := erf_range (value (-x).toBits) (not_lt.mp h2)
      have hy0 : 0 ≤ RealErf.erf (value (-x).toBits) := le_trans (by positivity) hy1
      generalize hR : Wasm.IEEE64.div (hornerW ppW (Wasm.IEEE64.mul (-x).toBits (-x).toBits))
        (hornerW qqW (Wasm.IEEE64.mul (-x).toBits (-x).toBits)) = R at hpos ⊢
      have hTf := finite_of_within_add (-x).toBits _ hPf _ hy0 hy2 hpos
      have hP0 : Wasm.IEEE64.scaledMagnitude (-x).toBits ≠ 0 := by
        intro h0
        have : value (-x).toBits = 0 := by
          simp only [value, Wasm.IEEE64.scaledValue, h0]
          split <;> simp
        have : (0 : ℝ) < 1 / 2 ^ 28 := by positivity
        linarith [not_lt.mp h2]
      have hRf := finite_of_mul_finite (-x).toBits R hPf hP0 hTf
      rw [mul_negate_left (-x).toBits R hPf hRf,
        add_negate (-x).toBits _ hPf hTf
          (add_ne_zero_of_within (-x).toBits _ _ hy1 hy2 hPf hTf hPs hpos)]
  · simp only [show ¬ _ from fun h => h1 (hsm.mp h), ↓reduceIte] at hpos ⊢
    by_cases h2 : value (-x).toBits < 5 / 4
    · simp only [hmid.mpr h2, ↓reduceIte] at hpos ⊢
      have hP28 : 1 / 2 ^ 28 ≤ value (-x).toBits := le_trans (by norm_num) (not_lt.mp h1)
      obtain ⟨hy1, hy2⟩ := erf_range (value (-x).toBits) hP28
      have hy0 : 0 ≤ RealErf.erf (value (-x).toBits) := le_trans (by positivity) hy1
      simp only [F64Bits.toBits_sub]
      rw [neg_ofBits _ ne]
      simp only [F64Bits.toBits_add, F64Bits.toBits_div, F64Bits.toBits_ofBits, ne,
        Bool.false_eq_true, ↓reduceIte] at hpos ⊢
      generalize hD : Wasm.IEEE64.div (Erf.erfMiddle ((-x).abs - 1.0)).1.toBits
        (Erf.erfMiddle ((-x).abs - 1.0)).2.toBits = D at hpos ⊢
      have hDf := finite_of_within_add _ _ hef _ hy0 hy2 hpos
      have hes : Wasm.IEEE64.sign (0x3FEB0AC160000000 : UInt64) = false := by decide
      exact add_negate _ _ hef hDf (add_ne_zero_of_within _ _ _ hy1 hy2 hef hDf hes hpos)
    · simp only [show ¬ _ from fun h => h2 (hmid.mp h), ↓reduceIte] at hpos ⊢
      by_cases h3 : 6 ≤ value (-x).toBits
      · simp only [hsix.mpr h3, ↓reduceIte] at hpos ⊢
        have ht1 : Wasm.IEEE64.sub 0x01A56E1FC2F8F359 0x3FF0000000000000 = 0xBFF0000000000000 := by
          decide +kernel
        have ht2 : Wasm.IEEE64.negate 0x3FF0000000000000 = 0xBFF0000000000000 := by decide
        simp only [F64Bits.toBits_sub, F64Bits.toBits_ofBits, nt, one_bits, Bool.false_eq_true,
          ↓reduceIte, ErfEnds.one_sub_tiny, ht1, ht2]
      · simp only [show ¬ _ from fun h => h3 (hsix.mp h), ↓reduceIte] at hpos ⊢
        have hP28 : 1 / 2 ^ 28 ≤ value (-x).toBits := le_trans (by norm_num) (not_lt.mp h1)
        obtain ⟨hy1, hy2⟩ := erf_range (value (-x).toBits) hP28
        have hy0 : 0 ≤ RealErf.erf (value (-x).toBits) := le_trans (by positivity) hy1
        simp only [F64Bits.toBits_sub, one_bits] at hpos ⊢
        generalize hq : (Erf.erfExp Exp.expTable (-x).abs
          (Erf.erfTail (1.0 / ((-x).abs * (-x).abs))
            ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E)).1
          (Erf.erfTail (1.0 / ((-x).abs * (-x).abs))
            ((x.toBits >>> 32 &&& 0x7fffffff) < 0x4006DB6E)).2 / (-x).abs).toBits = q at hpos ⊢
        have hone : Finite (0x3FF0000000000000 : UInt64) := ErfEnds.one_finite
        have hos : Wasm.IEEE64.sign (0x3FF0000000000000 : UInt64) = false := by decide
        have hnqf := finite_of_within_add _ _ hone _ hy0 hy2 hpos
        show Wasm.IEEE64.add q (Wasm.IEEE64.negate 0x3FF0000000000000) =
          Wasm.IEEE64.negate (Wasm.IEEE64.add 0x3FF0000000000000 (Wasm.IEEE64.negate q))
        rw [add_comm, ← add_negate _ _ hone hnqf
          (add_ne_zero_of_within _ _ _ hy1 hy2 hone hnqf hos hpos), F64RelativeStep.negate_negate]

/-- One step for `Erf.erfWith Exp.expTable x` for every finite `x`. -/
theorem erfWith_within_one (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value x.toBits)) (Erf.erfWith Exp.expTable x).toBits := by
  cases hs : Wasm.IEEE64.sign x.toBits
  · exact erf_pos x hxf hs
  · rw [erf_neg_bits x hxf hs]
    have hnx := neg_toBits x hxf
    have hPf : Finite (-x).toBits := by rw [hnx]; exact finite_negate _ hxf
    have hPs : Wasm.IEEE64.sign (-x).toBits = false := by
      rw [hnx, (F64Sign.fields_negate _).2.2, hs]
      rfl
    have hv : value x.toBits = -value (-x).toBits := by
      rw [hnx, (F64Magnitude.negate_value _ hxf).2, neg_neg]
    rw [hv, erf_neg]
    exact (F64SignedRounding.within_negate 1 _ _).mpr (erf_pos (-x) hPf hPs)

#print axioms erf_range
#print axioms erf_neg_bits
#print axioms erfWith_within_one

end Library.Numerics.Float64.Erf.ErfOdd
