import Verified.Examples.PowExpSpecial

/-!
The special paths of `Pow.powExp` with `signBias = 0` for `768 < |x| < 1024`.  The residual
`r` of `ExpFarRange.far_residual` stays within `1/256`, so the residual with the tail stays within
`1/128` and the evaluation within `1/64`.  For positive `x` the scale is at least `2 ^ 98`, the sum
at least `2 ^ 97`, and its product with `2 ^ 1009` is positive infinity; `exp L` reaches
`2 ^ 1024`.  For negative `x` the scale is at most `2 ^ -85`, the compensated sum of
`ExpSpecialNegative` applies, and `exp L` is at most `2 ^ -1100`.
-/

namespace Verified.Examples.PowExpFar
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude ExpSpecialNegative PowExpPaths

set_option exponentiation.threshold 4096

/-- The far state: the key, the residual with the tail, and the coarse evaluation. -/
theorem far_state (x xtail : Float) (hxf : Finite x.toBits) (htf : Finite xtail.toBits)
    (hx : |value x.toBits| ≤ 1024) (ht : |value xtail.toBits| ≤ 1 / 2 ^ 13) :
    ∃ (k q : Int) (j : Fin 128),
      k = 128 * q + j.val ∧
      ((ExpCoreState.shiftedBits x.toBits).toNat : Int) = (0x4338000000000000 : Int) + k ∧
      ((ExpCoreState.shiftedBits x.toBits) % 128).toNat = j.val ∧ k.natAbs ≤ 196609 ∧
      |value x.toBits - k * (Real.log 2 / 128)| ≤ 1 / 320 ∧
      Finite (PowExpCore.tmpFloat x xtail).toBits ∧
      |value (PowExpCore.tmpFloat x xtail).toBits| ≤ 1 / 64 := by
  obtain ⟨k, q, j, _, _, hk, _, hki, hj, hkn, hke⟩ := ExpFarRange.far_state x.toBits hxf hx
  have hid := ExpReductionBounds.ideal_residual_bound (value x.toBits) k hx hke
  obtain ⟨hrf, hrb⟩ := ExpFarRange.far_residual x.toBits hxf hx
  have hsum : |value (ExpResidualBounds.residual x.toBits) + value xtail.toBits| ≤
      1 / 256 + 1 / 2 ^ 13 := by
    have := abs_add_le (value (ExpResidualBounds.residual x.toBits)) (value xtail.toBits)
    linarith
  obtain ⟨hr'f, hr'e⟩ := F64AddBounds.add_real_relative _ _ hrf htf (hsum.trans_lt (by norm_num))
  have hr' : |value (Wasm.IEEE64.add (ExpResidualBounds.residual x.toBits) xtail.toBits)| ≤
      1 / 128 := by
    have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
    have h1 := hr'e.trans (mul_le_mul_of_nonneg_left hsum (by rw [hu]; positivity))
    have h2 := abs_sub_abs_le_abs_sub
      (value (Wasm.IEEE64.add (ExpResidualBounds.residual x.toBits) xtail.toBits))
      (value (ExpResidualBounds.residual x.toBits) + value xtail.toBits)
    rw [hu] at h1
    have h3 : (1 : ℝ) / 256 + 1 / 2 ^ 13 + 1 / 2 ^ 53 * (1 / 256 + 1 / 2 ^ 13) ≤ 1 / 128 := by
      norm_num
    linarith
  have hj' : ((ExpCoreBounds.floatShifted x).toBits % 128).toNat = j.val := by
    rw [ExpCoreBounds.floatShifted_bits]
    exact hj
  have htf' := (ExpTableBounds.entry_bounds j).2.1
  have htb := (ExpTableBounds.entry_bounds j).2.2.2.2
  have hev := PowExpEval.evaluation_coarse _ _ hr'f htf' hr' htb
  rw [← PowExpCore.tmp_bits x xtail j hj'] at hev
  exact ⟨k, q, j, hk, hki, hj, hkn, hid, hev.1, hev.2⟩

/-- The product of the scale with the coarse evaluation, and their sum. -/
theorem far_sum (s w : UInt64) (hsf : Finite s) (hwf : Finite w)
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000)
    (hw : |value w| ≤ 1 / 64) :
    Finite (Wasm.IEEE64.mul s w) ∧ |value (Wasm.IEEE64.mul s w)| ≤ value s / 32 ∧
      Finite (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) ∧
      value s / 2 ≤ value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) ∧
      value (Wasm.IEEE64.add s (Wasm.IEEE64.mul s w)) ≤ 2 * value s := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  have hprod : |value s * value w| ≤ value s / 64 := by
    rw [abs_mul, abs_of_pos hS]
    calc
      _ ≤ value s * (1 / 64) := mul_le_mul_of_nonneg_left hw hS.le
      _ = value s / 64 := by ring
  have hm := F64MulBounds.mul_real_mixed s w hsf hwf (by
    calc
      _ ≤ value s / 64 := hprod
      _ ≤ (2 : ℝ) ^ 1000 / 64 := div_le_div_of_nonneg_right hshi (by norm_num)
      _ < (2 : ℝ) ^ 1022 := by norm_num)
  have hmu : multiplicationUnderflowEpsilon ≤ value s / 2 ^ 60 := by
    calc
      _ ≤ (1 / (2 : ℝ) ^ 1000) / 2 ^ 60 := by norm_num [multiplicationUnderflowEpsilon]
      _ ≤ value s / 2 ^ 60 := div_le_div_of_nonneg_right hslo (by positivity)
  have hP : |value (Wasm.IEEE64.mul s w)| ≤ value s / 32 := by
    have h1 := hm.2
    have h2 := abs_sub_abs_le_abs_sub (value (Wasm.IEEE64.mul s w)) (value s * value w)
    have h3 : unitRoundoff64 * |value s * value w| ≤ 1 / 2 ^ 53 * (value s / 64) := by
      rw [hu]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    nlinarith
  have hsum : |value s + value (Wasm.IEEE64.mul s w)| ≤ value s + value s / 32 := by
    have := abs_add_le (value s) (value (Wasm.IEEE64.mul s w))
    rw [abs_of_pos hS] at this
    linarith
  obtain ⟨hyf, hye⟩ := F64AddBounds.add_real_relative s _ hsf hm.1 (by
    calc
      _ ≤ value s + value s / 32 := hsum
      _ ≤ (2 : ℝ) ^ 1000 + 2 ^ 1000 / 32 := by linarith
      _ < (2 : ℝ) ^ 1023 := by norm_num)
  have h1 := abs_le.mp hye
  have h2 := abs_le.mp hP
  have h3 : unitRoundoff64 * |value s + value (Wasm.IEEE64.mul s w)| ≤
      1 / 2 ^ 53 * (value s + value s / 32) := by
    rw [hu]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  refine ⟨hm.1, hP, hyf, ?_, ?_⟩ <;> nlinarith

/-- For `768 < x < 1024`, the result is positive infinity, within one step of `exp L`. -/
theorem far_positive (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits) (hxhi : |value x.toBits| < 1024) (hxpos : 768 < value x.toBits)
    (ht : |value xtail.toBits| ≤ 1 / 2 ^ 13)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ 1) :
    F64SignedRounding.WithinSteps 1 (Real.exp L)
      (Pow.powExpCore Exp.expTable x xtail 0 true).toBits := by
  obtain ⟨k, q, j, hk, hki, hj, hkn, hid, htmf, htmb⟩ :=
    far_state x xtail hxf htf hxhi.le ht
  have hq := ExpFarRange.far_quotient_pos _ k q j hk hid hxpos.le
  have hqb := ExpFarRange.quotient_bounds_far k q j hk hkn
  have hk0 : ¬ k < 0 := by have := j.isLt; omega
  have hguard : ExpCoreState.shiftedBits x.toBits &&& 0x80000000 = 0 := by
    simpa only [ite_eq_right hk0] using
      ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
  obtain ⟨hsf, hsv, hslo, hshi⟩ :=
    ExpSpecialScale.positive_scale_value _ k q j hki hk hj (by omega) (by omega)
  obtain ⟨_, _, hyf, hyl, _⟩ := far_sum _ _ hsf htmf hslo hshi htmb
  set s := ExpSpecialScale.positiveScale (ExpCoreState.shiftedBits x.toBits)
  set y := Wasm.IEEE64.add s (Wasm.IEEE64.mul s (PowExpCore.tmpFloat x xtail).toBits)
  obtain ⟨_, _, hH1, _, _⟩ := ExpTableBounds.entry_bounds j
  have hpow : (2 : ℝ) ^ (98 : Int) ≤ (2 : ℝ) ^ (q - 1009) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hS98 : (2 : ℝ) ^ (98 : Int) ≤ value s := by
    rw [hsv]
    calc
      (2 : ℝ) ^ (98 : Int) = (2 : ℝ) ^ (98 : Int) * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ (q - 1009) * value (ExpTableBounds.headBits j.val) :=
        mul_le_mul hpow hH1 (by norm_num) (by positivity)
  have h97 : (2 : ℝ) ^ (((1120 : Nat) : Int) - 1023) = (2 : ℝ) ^ (98 : Int) / 2 := by
    rw [show (((1120 : Nat) : Int) - 1023) = 98 - 1 by norm_num, zpow_sub₀ (by norm_num),
      zpow_one]
  have hy97 : (2 : ℝ) ^ (((1120 : Nat) : Int) - 1023) ≤ value y := by
    rw [h97]
    linarith
  have hey := exponent_ge_of_value y 1120 (by norm_num) hy97
  have hsmall : 1 / (2 : ℝ) ^ 1022 < (2 : ℝ) ^ (98 : Int) / 2 := by norm_num
  have hys := (normal_of_value y (by linarith)).2
  rw [PowExpCore.core_eq]
  simp only [ite_true]
  rw [PowExpSpecial.scale_word, ExpCoreBounds.floatShifted_bits,
    positive_bits (PowExpCore.tmpFloat x xtail)
      (ExpScaleBits.scaleBits (ExpCoreState.shiftedBits x.toBits))
      (ExpCoreState.shiftedBits x.toBits) (by rw [hguard]; rfl) hsf]
  change F64SignedRounding.WithinSteps 1 (Real.exp L) (Wasm.IEEE64.mul y 0x7F00000000000000)
  rw [ArmTight.mul_comm_finite y _ hyf (by unfold CodeLib.IEEE64.Finite; decide),
    ExpSpecialPositive.scale_up_word, F64PowerScale.mul_power_overflow 2032 y (by norm_num)
    (by norm_num) hyf (by omega) (by omega) (by omega), hys]
  apply Exp2Theorem.overflow_within
  apply exp_overflow
  have := abs_le.mp hL
  have := abs_le.mp ht
  linarith

/-- For `-1024 < x < -768`, the result lies within one step of `exp L`, whose reference is 0. -/
theorem far_negative (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits) (hxhi : |value x.toBits| < 1024) (hxneg : value x.toBits < -768)
    (ht : |value xtail.toBits| ≤ 1 / 2 ^ 13)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ 1) :
    F64SignedRounding.WithinSteps 1 (Real.exp L)
      (Pow.powExpCore Exp.expTable x xtail 0 true).toBits := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  obtain ⟨k, q, j, hk, hki, hj, hkn, hid, htmf, htmb⟩ :=
    far_state x xtail hxf htf hxhi.le ht
  have hq := ExpFarRange.far_quotient_neg _ k q j hk hid hxneg.le
  have hqb := ExpFarRange.quotient_bounds_far k q j hk hkn
  have hkneg : k < 0 := by have := j.isLt; omega
  have hguard := ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
  rw [ite_eq_left hkneg] at hguard
  have hg : ¬ (ExpCoreState.shiftedBits x.toBits &&& 0x80000000 == 0) = true := by
    rw [hguard]
    decide
  obtain ⟨hsf, hsv, hslo, hshi⟩ :=
    ExpSpecialScale.negative_scale_value _ k q j hki hk hj (by omega) (by omega)
  obtain ⟨hpf, hPm, hyf, hyl, hyu⟩ := far_sum _ _ hsf htmf hslo hshi htmb
  set s := ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits) with hsdef
  set p := Wasm.IEEE64.mul s (PowExpCore.tmpFloat x xtail).toBits
  obtain ⟨_, _, _, hH2, _⟩ := ExpTableBounds.entry_bounds j
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  have hS85 : value s ≤ 1 / (2 : ℝ) ^ 85 := by
    have hpow : (2 : ℝ) ^ (q + 1022) ≤ (2 : ℝ) ^ (-86 : Int) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h86 : (2 : ℝ) ^ (-86 : Int) * 2 = 1 / (2 : ℝ) ^ 85 := by norm_num
    rw [hsv, ← h86]
    exact mul_le_mul hpow hH2 (by linarith) (by positivity)
  have hy1 : value (Wasm.IEEE64.add s p) < 1 := by
    have : (2 : ℝ) / 2 ^ 85 < 1 := by norm_num
    linarith
  have hypos : 0 < value (Wasm.IEEE64.add s p) := by linarith
  rw [PowExpCore.core_eq]
  simp only [ite_true]
  rw [PowExpSpecial.scale_word, ExpCoreBounds.floatShifted_bits]
  have hsd : ExpScaleBits.scaleBits (ExpCoreState.shiftedBits x.toBits) +
      ((1022 : UInt64) <<< (52 : UInt64)) = s := rfl
  rw [negative_bits (PowExpCore.tmpFloat x xtail)
      (ExpScaleBits.scaleBits (ExpCoreState.shiftedBits x.toBits))
      (ExpCoreState.shiftedBits x.toBits) hg (by rw [hsd]; exact hsf)
      (by rw [hsd]; exact sign_of_pos _ hS) (by rw [hsd]; exact hyf) (by rw [hsd]; exact hypos),
    hsd]
  rw [lt_one_iff _ hyf, decide_eq_true hy1, ite_eq_left rfl]
  have hE := Real.exp_pos L
  have hLb : L ≤ -763 := by
    have := abs_le.mp hL
    have := abs_le.mp ht
    linarith
  have hEt := exp_tiny L hLb
  have hTE : (2 : ℝ) ^ (1022 : Int) * Real.exp L ≤ 1 / (2 : ℝ) ^ 78 := by
    rw [two_zpow_1022]
    calc
      _ ≤ (2 : ℝ) ^ 1022 * (1 / (2 : ℝ) ^ 1100) := mul_le_mul_of_nonneg_left hEt (by positivity)
      _ = 1 / (2 : ℝ) ^ 78 := by
        rw [show (2 : ℝ) ^ 1100 = 2 ^ 1022 * 2 ^ 78 by rw [← pow_add]]
        field_simp
  have hTE0 : 0 ≤ (2 : ℝ) ^ (1022 : Int) * Real.exp L := by positivity
  have hPb := abs_le.mp hPm
  have hpre : |value s + value p - (2 : ℝ) ^ (1022 : Int) * Real.exp L| ≤
      11 / 16 * unitRoundoff64 := by
    have h1 : (1 : ℝ) / 2 ^ 85 + 1 / 2 ^ 85 / 32 ≤ 1 / 2 ^ 78 := by norm_num
    have h2 : (1 : ℝ) / 2 ^ 78 ≤ 11 / 16 * (1 / 2 ^ 53) := by norm_num
    rw [hu, abs_le]
    constructor <;> nlinarith
  have hPm32 : |value p| ≤ value s / 32 := hPm
  obtain ⟨hclim, hc1, hc2⟩ := compensated_one_step s p _ hsf hpf hS hshi hPm32 hy1 hE hpre
  exact F64SignedRounding.within_of_nonneg 1 _ hE.le _ hclim.le hc1 hc2

#print axioms far_state
#print axioms far_sum
#print axioms far_positive
#print axioms far_negative

end Verified.Examples.PowExpFar
