import Verified.Examples.AtanTwoBits

/-!
`Atan.atan2 y x` within two steps of `Complex.arg (x + y i)` for finite `x` and finite nonzero
`y`.  The proof follows the code's branches.  For `x = 1` the result is `atan y`, within one step
of `arctan y`.  For `x = ±0` the result is `±π/2` rounded.  When the high words put `|y/x|` above
`2 ^ 60` the result is `±π/2` rounded, and when `x < 0` and they put `|y/x|` below `2 ^ -59` it is
`±π` rounded; the argument lies within `2 ^ -59` of these values.  Otherwise `AtanTwoAtan` bounds
`atan |y/x|` against `arctan Q` for the exact `Q = |y/x|`, and the quadrant gives the sign and,
for `x < 0`, the subtraction from `π` (`AtanTwoErr.neg_finish`).
-/

namespace Verified.Examples.AtanTwoTheorem
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches AtanTwoBranches AtanTwoBits AtanTwoErr

set_option exponentiation.threshold 4096

theorem arctan_nonneg (v : ℝ) (hv : 0 ≤ v) : 0 ≤ Real.arctan v :=
  AtanTwoAtan.arctan_nonneg v hv

/-- `arctan t = π/2 - arctan (1/t)` within `1/t` of `π/2` for `t > 0`. -/
theorem arctan_near_half (t : ℝ) (ht : 0 < t) :
    Real.pi / 2 - 1 / t ≤ Real.arctan t ∧ Real.arctan t ≤ Real.pi / 2 := by
  have hinv := Real.arctan_inv_of_pos ht
  have h0 : 0 ≤ Real.arctan t⁻¹ := arctan_nonneg _ (inv_nonneg.mpr ht.le)
  have h1 : Real.arctan t⁻¹ ≤ 1 / t := by
    have := AtanTheoremConst.abs_arctan_le t⁻¹
    rw [abs_of_nonneg h0, abs_of_nonneg (inv_nonneg.mpr ht.le)] at this
    rw [one_div]
    exact this
  constructor <;> linarith

theorem arg_imag_pos (v : ℝ) (hv : 0 < v) :
    Complex.arg (((0 : ℝ) : ℂ) + (v : ℂ) * Complex.I) = Real.pi / 2 := by
  rw [Complex.ofReal_zero, zero_add, Complex.arg_real_mul _ hv, Complex.arg_I]

theorem arg_imag_neg (v : ℝ) (hv : v < 0) :
    Complex.arg (((0 : ℝ) : ℂ) + (v : ℂ) * Complex.I) = -(Real.pi / 2) := by
  rw [Complex.ofReal_zero, zero_add,
    show (v : ℂ) * Complex.I = ((-v : ℝ) : ℂ) * (-Complex.I) by push_cast; ring,
    Complex.arg_real_mul _ (by linarith), Complex.arg_neg_I]

/-- Two steps from `π/2` rounded for a number within `2 ^ -59` of `π/2`. -/
theorem within_half (A : ℝ) (hA : |A - Real.pi / 2| ≤ 1 / 2 ^ 59) :
    F64SignedRounding.WithinSteps 2 A (0x3FF921FB54442D18 : UInt64) := by
  have hc := AtanTheorem.big_close
  have hp := AtanTheoremConst.pi_close
  rw [abs_le] at hc hp hA
  have herr : |value (0x3FF921FB54442D18 : UInt64) - A| ≤ 62 / 10 ^ 18 + 1 / 2 ^ 59 := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, hA.1, hA.2]
  have hf : Finite (0x3FF921FB54442D18 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  refine F64TwoSteps.within_two_of_error _ _ 1023 (by norm_num) (by norm_num) _ hf herr ?_
    (by norm_num)
  rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num)]
  norm_num
  linarith [hp.1, hp.2, hA.1]

/-- Two steps from `π` rounded for a number within `2 ^ -58` of `π`. -/
theorem within_pi (A : ℝ) (hA : |A - Real.pi| ≤ 1 / 2 ^ 58) :
    F64SignedRounding.WithinSteps 2 A (0x400921FB54442D18 : UInt64) := by
  have hp := AtanTheoremConst.pi_close
  have hv : value (0x400921FB54442D18 : UInt64) = 884279719003555 / 2 ^ 48 := by
    rw [AtanTheoremCases.word_eq 0x400921FB54442D18 (884279719003555 / 2 ^ 48) (by decide +kernel)]
    norm_num
  rw [abs_le] at hp hA
  have herr : |value (0x400921FB54442D18 : UInt64) - A| ≤ 13 / 10 ^ 17 + 1 / 2 ^ 58 := by
    rw [hv, abs_le]
    constructor <;> linarith [hp.1, hp.2, hA.1, hA.2]
  have hf : Finite (0x400921FB54442D18 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  refine F64TwoSteps.within_two_of_error _ _ 1024 (by norm_num) (by norm_num) _ hf herr ?_
    (by norm_num)
  rw [F64PositiveSpacing.boundary_value 1024 (by norm_num) (by norm_num)]
  norm_num
  linarith [hp.1, hp.2, hA.1]

theorem within_neg (n : ℕ) (A : ℝ) (w : UInt64) (h : F64SignedRounding.WithinSteps n A w) :
    F64SignedRounding.WithinSteps n (-A) (Wasm.IEEE64.negate w) :=
  (F64SignedRounding.within_negate n A w).mpr h

theorem neg_float (z : Float) (h : Wasm.IEEE64.isNaN z.toBits = false) :
    (-z).toBits = Wasm.IEEE64.negate z.toBits := by
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, h]
  simp only [Bool.false_eq_true, ite_false]

/-- `|a| < 2 ^ (ea - eb) |b|` from the exponent fields. -/
theorem ratio_lt (a b : Float) (ea eb : ℕ) (hea : 1 ≤ ea) (heb : 1 ≤ eb) (heb2 : eb < 2048)
    (ha : Wasm.IEEE64.exponent a.toBits < ea) (hb : eb ≤ Wasm.IEEE64.exponent b.toBits) :
    |value a.toBits| < 2 ^ ((ea : ℤ) - eb) * |value b.toBits| := by
  have h1 := F64Magnitude.magnitude_lt a.toBits ea ((ea : ℤ) - 1023) hea (by ring) ha
  have h2 := F64Magnitude.magnitude_ge b.toBits eb ((eb : ℤ) - 1023) heb heb2 (by ring) hb
  have h3 : (2 : ℝ) ^ ((ea : ℤ) - 1023) = 2 ^ ((ea : ℤ) - eb) * 2 ^ ((eb : ℤ) - 1023) := by
    rw [← zpow_add₀ (by norm_num)]
    congr 1
    ring
  calc |value a.toBits| < 2 ^ ((ea : ℤ) - 1023) := h1
    _ = 2 ^ ((ea : ℤ) - eb) * 2 ^ ((eb : ℤ) - 1023) := h3
    _ ≤ 2 ^ ((ea : ℤ) - eb) * |value b.toBits| := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem pos_of_sign (w : UInt64) (hs : Wasm.IEEE64.sign w = false) (h0 : value w ≠ 0) :
    0 < value w :=
  lt_of_le_of_ne (nonneg_of_sign w hs) (Ne.symm h0)

theorem neg_of_sign (w : UInt64) (hs : Wasm.IEEE64.sign w = true) (h0 : value w ≠ 0) :
    value w < 0 :=
  (F64Magnitude.sign_value w (F64RoundDouble.mag_pos w h0)).mp hs

/-- `x = ±0`. -/
theorem xzero_case (y : Float) (hy0 : value y.toBits ≠ 0) :
    F64SignedRounding.WithinSteps 2
      (Complex.arg (((0 : ℝ) : ℂ) + (value y.toBits : ℂ) * Complex.I))
      (if y.toBits >>> 32 >>> 31 == 1 then
        -Float.ofBits 0x3FF921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359
      else Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359).toBits := by
  rw [F64UpperWord.sign_test]
  cases hs : Wasm.IEEE64.sign y.toBits
  · rw [if_neg (by decide), half_bits, arg_imag_pos _ (pos_of_sign _ hs hy0)]
    exact within_half _ (by rw [sub_self, abs_zero]; positivity)
  · rw [if_pos rfl, half_neg_bits, arg_imag_neg _ (neg_of_sign _ hs hy0)]
    exact within_neg 2 _ _ (within_half _ (by rw [sub_self, abs_zero]; positivity))

/-- `|y/x|` above `2 ^ 60`. -/
theorem big_case (y x : Float) (hy : Finite y.toBits) (hx : Finite x.toBits)
    (hy0 : value y.toBits ≠ 0) (hx0 : value x.toBits ≠ 0)
    (hk : (ixOf x).toNat + 61 * 2 ^ 20 ≤ (ixOf y).toNat) :
    F64SignedRounding.WithinSteps 2
      (Complex.arg ((value x.toBits : ℂ) + (value y.toBits : ℂ) * Complex.I))
      (quadTail (Float.ofBits 0x3FF921FB54442D18 + 0.5 * piLoF) (mOf y x &&& 1)).toBits := by
  have hey := exp_ix y
  have hex := exp_ix x
  have hfy : Wasm.IEEE64.exponent y.toBits < 2047 := by
    have := F64UpperWord.finite_high y.toBits hy
    have : (ixOf y).toNat < 0x7ff00000 := this
    omega
  have hr := ratio_lt x y (Wasm.IEEE64.exponent x.toBits + 1) (Wasm.IEEE64.exponent y.toBits)
    (by omega) (by omega) (by omega) (by omega) le_rfl
  have hz : (2 : ℝ) ^ (((Wasm.IEEE64.exponent x.toBits + 1 : ℕ) : ℤ) -
      (Wasm.IEEE64.exponent y.toBits : ℕ)) ≤ 2 ^ (-60 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
  have hay : 0 < |value y.toBits| := abs_pos.mpr hy0
  have hxy : |value x.toBits| ≤ |value y.toBits| / 2 ^ 60 := by
    have := mul_le_mul_of_nonneg_right hz hay.le
    rw [show (2 : ℝ) ^ (-60 : ℤ) = 1 / 2 ^ 60 by norm_num] at this
    rw [div_eq_mul_one_div, mul_comm]
    linarith
  have hm1 := m_one_toNat y x
  have hyN := y.toBits.toNat_lt
  obtain ⟨hsT, hsF⟩ := sign_toNat y.toBits
  cases hs : Wasm.IEEE64.sign y.toBits
  · have hyp := pos_of_sign _ hs hy0
    have hm : mOf y x &&& 1 = 0 := by
      apply UInt64.toNat_inj.mp
      rw [hm1, hsF.mp hs]
      rfl
    rw [hm, quad_zero, big_bits2]
    apply within_half
    rw [abs_of_pos hyp] at hxy
    rcases lt_or_gt_of_ne hx0 with hxn | hxp
    · rw [AtanTwoArg.arg_of_neg_of_pos _ _ hxn hyp]
      have hq : value y.toBits / value x.toBits = -(value y.toBits / -value x.toBits) := by
        rw [div_neg, neg_neg]
      have ht : 0 < value y.toBits / -value x.toBits := div_pos hyp (by linarith)
      obtain ⟨h1, h2⟩ := arctan_near_half _ ht
      have h3 : 1 / (value y.toBits / -value x.toBits) ≤ 1 / 2 ^ 60 := by
        rw [one_div_div, div_le_div_iff₀ hyp (by positivity)]
        rw [abs_of_neg hxn] at hxy
        rw [le_div_iff₀ (by positivity)] at hxy
        linarith
      rw [hq, Real.arctan_neg, abs_le]
      constructor <;> linarith
    · rw [AtanTwoArg.arg_of_pos _ _ hxp]
      have ht : 0 < value y.toBits / value x.toBits := div_pos hyp hxp
      obtain ⟨h1, h2⟩ := arctan_near_half _ ht
      have h3 : 1 / (value y.toBits / value x.toBits) ≤ 1 / 2 ^ 60 := by
        rw [one_div_div, div_le_div_iff₀ hyp (by positivity)]
        rw [abs_of_pos hxp] at hxy
        rw [le_div_iff₀ (by positivity)] at hxy
        linarith
      rw [abs_le]
      constructor <;> linarith
  · have hyn := neg_of_sign _ hs hy0
    have hm : mOf y x &&& 1 = 1 := by
      apply UInt64.toNat_inj.mp
      rw [hm1, hsT.mp hs]
      rfl
    rw [hm, quad_one, big_neg_bits2]
    rw [abs_of_neg hyn] at hxy
    have hmid : |-Complex.arg ((value x.toBits : ℂ) + (value y.toBits : ℂ) * Complex.I) -
        Real.pi / 2| ≤ 1 / 2 ^ 59 := by
      rcases lt_or_gt_of_ne hx0 with hxn | hxp
      · rw [AtanTwoArg.arg_of_neg_of_neg _ _ hxn hyn]
        have hq : value y.toBits / value x.toBits = -value y.toBits / -value x.toBits :=
          (neg_div_neg_eq _ _).symm
        have ht : 0 < -value y.toBits / -value x.toBits := div_pos (by linarith) (by linarith)
        obtain ⟨h1, h2⟩ := arctan_near_half _ ht
        have h3 : 1 / (-value y.toBits / -value x.toBits) ≤ 1 / 2 ^ 60 := by
          rw [one_div_div, div_le_div_iff₀ (by linarith) (by positivity)]
          rw [abs_of_neg hxn] at hxy
          rw [le_div_iff₀ (by positivity)] at hxy
          linarith
        rw [hq, abs_le]
        constructor <;> linarith [Real.pi_pos]
      · rw [AtanTwoArg.arg_of_pos _ _ hxp]
        have hq : value y.toBits / value x.toBits = -(-value y.toBits / value x.toBits) := by
          rw [neg_div, neg_neg]
        have ht : 0 < -value y.toBits / value x.toBits := div_pos (by linarith) hxp
        obtain ⟨h1, h2⟩ := arctan_near_half _ ht
        have h3 : 1 / (-value y.toBits / value x.toBits) ≤ 1 / 2 ^ 60 := by
          rw [one_div_div, div_le_div_iff₀ (by linarith) (by positivity)]
          rw [abs_of_pos hxp] at hxy
          rw [le_div_iff₀ (by positivity)] at hxy
          linarith
        rw [hq, Real.arctan_neg, neg_neg, abs_le]
        constructor <;> linarith
    have h := within_neg 2 _ _ (within_half _ hmid)
    rwa [neg_neg] at h

/-- `x < 0` and `|y/x|` below `2 ^ -59`. -/
theorem tiny_case (y x : Float) (hy : Finite y.toBits) (hx : Finite x.toBits)
    (hy0 : value y.toBits ≠ 0) (hx0 : value x.toBits ≠ 0) (hsx : Wasm.IEEE64.sign x.toBits = true)
    (hk : (ixOf y).toNat + 60 * 2 ^ 20 < (ixOf x).toNat) :
    F64SignedRounding.WithinSteps 2
      (Complex.arg ((value x.toBits : ℂ) + (value y.toBits : ℂ) * Complex.I))
      (quadTail 0.0 (mOf y x)).toBits := by
  have hey := exp_ix y
  have hex := exp_ix x
  have hfx : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have := F64UpperWord.finite_high x.toBits hx
    have : (ixOf x).toNat < 0x7ff00000 := this
    omega
  have hr := ratio_lt y x (Wasm.IEEE64.exponent y.toBits + 1) (Wasm.IEEE64.exponent x.toBits)
    (by omega) (by omega) (by omega) (by omega) le_rfl
  have hz : (2 : ℝ) ^ (((Wasm.IEEE64.exponent y.toBits + 1 : ℕ) : ℤ) -
      (Wasm.IEEE64.exponent x.toBits : ℕ)) ≤ 2 ^ (-59 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
  have hxn := neg_of_sign _ hsx hx0
  have hax : 0 < |value x.toBits| := abs_pos.mpr hx0
  have hq : |value y.toBits / value x.toBits| ≤ 1 / 2 ^ 59 := by
    rw [abs_div, div_le_iff₀ hax]
    have := mul_le_mul_of_nonneg_right hz hax.le
    rw [show (2 : ℝ) ^ (-59 : ℤ) = 1 / 2 ^ 59 by norm_num] at this
    linarith
  have hat := AtanTheoremConst.abs_arctan_le (value y.toBits / value x.toBits)
  have hm := m_toNat y x
  have hyN := y.toBits.toNat_lt
  obtain ⟨hsT, hsF⟩ := sign_toNat y.toBits
  have hxT := (sign_toNat x.toBits).1.mp hsx
  cases hs : Wasm.IEEE64.sign y.toBits
  · have hyp := pos_of_sign _ hs hy0
    have hm2 : mOf y x = 2 := by
      apply UInt64.toNat_inj.mp
      rw [hm, hsF.mp hs, hxT]
      rfl
    rw [hm2, quad_two, pi_bits, AtanTwoArg.arg_of_neg_of_pos _ _ hxn hyp]
    apply within_pi
    rw [show Real.arctan (value y.toBits / value x.toBits) + Real.pi - Real.pi =
      Real.arctan (value y.toBits / value x.toBits) by ring]
    linarith
  · have hyn := neg_of_sign _ hs hy0
    have hm3 : mOf y x = 3 := by
      apply UInt64.toNat_inj.mp
      rw [hm, hsT.mp hs, hxT]
      rfl
    rw [hm3, quad_three, pi_neg_bits, AtanTwoArg.arg_of_neg_of_neg _ _ hxn hyn]
    have h := within_neg 2 _ _ (within_pi (-(Real.arctan (value y.toBits / value x.toBits) -
      Real.pi)) (by
        rw [show -(Real.arctan (value y.toBits / value x.toBits) - Real.pi) - Real.pi =
          -Real.arctan (value y.toBits / value x.toBits) by ring, abs_neg]
        linarith))
    rwa [neg_neg] at h

/-- The general branch. -/
theorem gen_case (y x : Float) (hy : Finite y.toBits) (hx : Finite x.toBits)
    (hy0 : value y.toBits ≠ 0) (hx0 : value x.toBits ≠ 0)
    (hQ : |value y.toBits / value x.toBits| < 2 ^ 1022) :
    F64SignedRounding.WithinSteps 2
      (Complex.arg ((value x.toBits : ℂ) + (value y.toBits : ℂ) * Complex.I))
      (quadTail (Atan.atan (y / x).abs) (mOf y x)).toBits := by
  obtain ⟨hqf, hqQ⟩ := AtanTwoQuot.quot_facts y x hy hx hx0 hQ
  have hsq : Wasm.IEEE64.sign (y / x).abs.toBits = false := by
    rw [F64Bits.toBits_abs]
    exact (F64Sign.fields_abs _).2.2
  obtain ⟨hzf, hzD, hzW⟩ := AtanTwoAtan.atan_good _ hqf hsq _ (abs_nonneg _) hqQ
  have hA0 := arctan_nonneg _ (abs_nonneg (value y.toBits / value x.toBits))
  have hA1 := (Real.arctan_lt_pi_div_two |value y.toBits / value x.toBits|).le
  have hneg := neg_finish _ hzf _ _ hA0 hA1 hzD le_rfl
  have hm := m_toNat y x
  obtain ⟨hyT, hyF⟩ := sign_toNat y.toBits
  obtain ⟨hxT, hxF⟩ := sign_toNat x.toBits
  cases hsx : Wasm.IEEE64.sign x.toBits <;> cases hsy : Wasm.IEEE64.sign y.toBits
  · have hxp := pos_of_sign _ hsx hx0
    have hyp := pos_of_sign _ hsy hy0
    have hm0 : mOf y x = 0 := by
      apply UInt64.toNat_inj.mp
      rw [hm, hyF.mp hsy, hxF.mp hsx]
      rfl
    rw [hm0, quad_zero, AtanTwoArg.arg_of_pos _ _ hxp]
    rw [abs_of_pos (div_pos hyp hxp)] at hzW
    exact hzW
  · have hxp := pos_of_sign _ hsx hx0
    have hyn := neg_of_sign _ hsy hy0
    have hm1 : mOf y x = 1 := by
      apply UInt64.toNat_inj.mp
      rw [hm, hyT.mp hsy, hxF.mp hsx]
      rfl
    rw [hm1, quad_one, AtanTwoArg.arg_of_pos _ _ hxp,
      neg_float _ (AtanTheorem.not_nan_of_within 2 _ _ hzW)]
    rw [abs_of_neg (div_neg_of_neg_of_pos hyn hxp), Real.arctan_neg] at hzW
    have h := within_neg 2 _ _ hzW
    rwa [neg_neg] at h
  · have hxn := neg_of_sign _ hsx hx0
    have hyp := pos_of_sign _ hsy hy0
    have hm2 : mOf y x = 2 := by
      apply UInt64.toNat_inj.mp
      rw [hm, hyF.mp hsy, hxT.mp hsx]
      rfl
    rw [hm2, quad_two, AtanTwoArg.arg_of_neg_of_pos _ _ hxn hyp]
    rw [abs_of_neg (div_neg_of_pos_of_neg hyp hxn)] at hneg
    rw [show Real.arctan (value y.toBits / value x.toBits) + Real.pi =
      Real.pi - Real.arctan (-(value y.toBits / value x.toBits)) by rw [Real.arctan_neg]; ring]
    exact hneg.1
  · have hxn := neg_of_sign _ hsx hx0
    have hyn := neg_of_sign _ hsy hy0
    have hm3 : mOf y x = 3 := by
      apply UInt64.toNat_inj.mp
      rw [hm, hyT.mp hsy, hxT.mp hsx]
      rfl
    rw [hm3, quad_three, AtanTwoArg.arg_of_neg_of_neg _ _ hxn hyn]
    rw [abs_of_pos (div_pos_of_neg_of_neg hyn hxn)] at hneg
    exact hneg.2

/-- `|y/x| < 2 ^ 1022` in the general branch, where the exponent of `y` exceeds that of `x` by
at most 61. -/
theorem quot_lt (y x : Float) (hy : Finite y.toBits) (hx0 : value x.toBits ≠ 0)
    (hk : (ixOf y).toNat < (ixOf x).toNat + 61 * 2 ^ 20) :
    |value y.toBits / value x.toBits| < 2 ^ 1022 := by
  have hey := exp_ix y
  have hex := exp_ix x
  have hix := ix_lt x
  have hiy := ix_lt y
  have hax : 0 < |value x.toBits| := abs_pos.mpr hx0
  rw [abs_div, div_lt_iff₀ hax]
  rcases Nat.eq_zero_or_pos (Wasm.IEEE64.exponent x.toBits) with h0 | h1
  · have hy62 := F64Magnitude.magnitude_lt y.toBits 62 (-961) (by norm_num) (by norm_num)
      (by omega)
    have hxm : (1 : ℝ) / 2 ^ 1074 ≤ |value x.toBits| := by
      rw [F64RoundNearest.abs_value, div_le_div_iff_of_pos_right (by positivity)]
      exact_mod_cast F64RoundDouble.mag_pos _ hx0
    rw [show (2 : ℝ) ^ (-961 : ℤ) = 1 / 2 ^ 961 by norm_num] at hy62
    have h3 : (1 : ℝ) / 2 ^ 961 ≤ 2 ^ 1022 * (1 / 2 ^ 1074) := by norm_num
    have h4 := mul_le_mul_of_nonneg_left hxm (by positivity : (0 : ℝ) ≤ 2 ^ 1022)
    linarith
  · have hr := ratio_lt y x (Wasm.IEEE64.exponent y.toBits + 1) (Wasm.IEEE64.exponent x.toBits)
      (by omega) h1 (by omega) (by omega) le_rfl
    have hz : (2 : ℝ) ^ (((Wasm.IEEE64.exponent y.toBits + 1 : ℕ) : ℤ) -
        (Wasm.IEEE64.exponent x.toBits : ℕ)) ≤ 2 ^ (62 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
    have h4 := mul_le_mul_of_nonneg_right hz hax.le
    have h5 : (2 : ℝ) ^ (62 : ℤ) * |value x.toBits| ≤ 2 ^ 1022 * |value x.toBits| :=
      mul_le_mul_of_nonneg_right (by norm_num) hax.le
    linarith

/-- **`atan2` within two steps.**  For finite `x` and finite nonzero `y`, `Atan.atan2 y x` lies
within two representable steps of the nearest-even reference of `arg (x + y i)`. -/
theorem atan2_within_two (y x : Float) (hy : Finite y.toBits) (hx : Finite x.toBits)
    (hy0 : value y.toBits ≠ 0) :
    F64SignedRounding.WithinSteps 2
      (Complex.arg ((value x.toBits : ℂ) + (value y.toBits : ℂ) * Complex.I))
      (Atan.atan2 y x).toBits := by
  have hn := not_nan y x hy hx
  by_cases h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = true
  · rw [atan2_one_eq y x hn h1, one_test x h1, AtanTwoArg.arg_of_pos 1 _ one_pos, div_one]
    have h := AtanTheorem.atan_within_one y hy
    exact ⟨h.1, h.2.trans (by norm_num)⟩
  have h1' : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false := by simpa using h1
  have h2 : (ixOf y ||| lxOf y == 0) = false := by
    rw [zero_test, decide_eq_false_iff_not]
    exact hy0
  by_cases hx0 : value x.toBits = 0
  · have h3 : (ixOf x ||| lxOf x == 0) = true := by
      rw [zero_test, decide_eq_true_eq]
      exact hx0
    rw [atan2_xzero_eq y x hn h1' h2 h3, hx0]
    exact xzero_case y hy0
  have h3 : (ixOf x ||| lxOf x == 0) = false := by
    rw [zero_test, decide_eq_false_iff_not]
    exact hx0
  have h4 := inf_test x hx
  have h5 := inf_test y hy
  by_cases h6 : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = true
  · rw [atan2_big_eq y x hn h1' h2 h3 h4 h5 h6]
    exact big_case y x hy hx hy0 hx0 (big_cond y x h6)
  have h6' : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = false := by simpa using h6
  by_cases h7 : (x.toBits >>> 32 >>> 31 == 1 && kOf2 y x >>> 63 == 1 &&
      decide (kOf2 y x < 0xFFFFFFFFFFFFFFC4)) = true
  · rw [atan2_tiny_eq y x hn h1' h2 h3 h4 h5 h6' h7]
    obtain ⟨hsx, hk⟩ := tiny_cond y x h7
    exact tiny_case y x hy hx hy0 hx0 hsx hk
  have h7' : (x.toBits >>> 32 >>> 31 == 1 && kOf2 y x >>> 63 == 1 &&
      decide (kOf2 y x < 0xFFFFFFFFFFFFFFC4)) = false := by simpa using h7
  rw [atan2_gen_eq y x hn h1' h2 h3 h4 h5 h6' h7']
  exact gen_case y x hy hx hy0 hx0 (quot_lt y x hy hx0 (nbig_cond y x h6'))

#print axioms atan2_within_two

end Verified.Examples.AtanTwoTheorem
