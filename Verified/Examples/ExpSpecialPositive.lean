import Verified.Examples.ExpSpecialPositiveCore
import Verified.Examples.ExpOneStep
import LeanExe.ProofKit.F64PowerScale

/-!
The positive special path of `Exp.exp`.  For finite `512 ≤ a ≤ 768`, the result is the product of
`2 ^ 1009` and the reconstruction, which is exact or positive infinity, and it lies within one
step of the nonnegative nearest-even reference of `exp a`, overflow included.
-/

namespace Verified.Examples.ExpSpecialPositive
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative

set_option exponentiation.threshold 4096

theorem scale_up_word : (0x7F00000000000000 : UInt64) = Wasm.IEEE64.encodeFinite false 2032 0 := by
  decide

theorem infinity_word :
    Wasm.IEEE64.infinity false = F64PositiveRounding.positiveInfinity := by
  decide

/-- A word with value above `2 ^ -1022` is normal and positive. -/
theorem normal_of_value (y : UInt64) (hy : 1 / (2 : ℝ) ^ 1022 < value y) :
    1 ≤ Wasm.IEEE64.exponent y ∧ Wasm.IEEE64.sign y = false := by
  constructor
  · by_contra h
    have hm := F64ExponentBounds.magnitude_le_boundary y 1 (by norm_num) (by omega)
    have hb : value (F64ExponentBounds.boundary 1) = (2 : ℝ) ^ (-1022 : Int) :=
      F64NearestBinade.boundary_power 1 (-1022) le_rfl (by norm_num) (by norm_num)
    have hp : (2 : ℝ) ^ (-1022 : Int) = 1 / (2 : ℝ) ^ 1022 := by norm_num
    rw [hb, hp, abs_of_pos (by positivity)] at hm
    have := le_abs_self (value y)
    linarith
  · by_contra h
    have hs : Wasm.IEEE64.sign y = true := by simpa using h
    have hv : value y ≤ 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast]
      have : (0 : ℝ) ≤ (Wasm.IEEE64.scaledMagnitude y : ℝ) / (2 : ℝ) ^ 1074 := by positivity
      rw [neg_div]
      linarith
    have : (0 : ℝ) < 1 / (2 : ℝ) ^ 1022 := by positivity
    linarith

/-- A positive word whose exponent field is at least `e` has value at least `2 ^ (e - 1023)`. -/
theorem value_ge_of_exponent (y : UInt64) (e : Nat) (q : Int) (he : 1 ≤ e) (he' : e < 2048)
    (heq : (e : Int) = q + 1023) (hs : Wasm.IEEE64.sign y = false)
    (hye : e ≤ Wasm.IEEE64.exponent y) : (2 : ℝ) ^ q ≤ value y := by
  have hb : value (F64ExponentBounds.boundary e) = (2 : ℝ) ^ q :=
    F64NearestBinade.boundary_power e q he he' heq
  have hnn : 0 ≤ value y := by
    simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Int.cast_natCast]
    positivity
  by_contra h
  have hlt : |value y| < |value (F64ExponentBounds.boundary e)| := by
    rw [hb, abs_of_nonneg hnn, abs_of_pos (zpow_pos (by norm_num) q)]
    exact lt_of_not_ge h
  have := F64ExponentBounds.exponent_lt_of_magnitude_lt y e he' hlt
  omega

theorem positive_one_step (x : Float) (hxf : Finite x.toBits)
    (hx : |value x.toBits| ≤ 768) (hxpos : 512 ≤ value x.toBits) :
    (Exp.exp x).toBits.toNat ≤ limit ∧
      (Exp.exp x).toBits.toNat ≤
        (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat ≤
        (Exp.exp x).toBits.toNat + 1 := by
  let Y := ExpSpecialReconstruction.floatReconstruction ExpSpecialScale.positiveScale x
  have hexp : (Exp.exp x).toBits = Wasm.IEEE64.mul 0x7F00000000000000 Y.toBits := by
    rw [ExpSpecialPositiveCore.exp_positive_eq x hxf hx hxpos, F64Bits.toBits_mul,
      F64Bits.toBits_ofBits]
    simp only [show Wasm.IEEE64.isNaN 0x7F00000000000000 = false by decide, Bool.false_eq_true,
      ite_false]
    rfl
  obtain ⟨k, q, j, hkv, hk, _, hki, hj, hkn⟩ := ExpCoreState.prefix_state x.toBits hxf hx
  have hq9 := ExpSpecialScale.positive_quotient x.toBits k q j hxf hx hxpos hkv hk
  have hqb := ExpSpecialScale.quotient_bounds k q j hk hkn
  obtain ⟨_, hsv, _, _⟩ :=
    ExpSpecialScale.positive_scale_value _ k q j hki hk hj hq9 (hqb.2.trans (by norm_num))
  obtain ⟨hYf, hYe⟩ := ExpSpecialReconstruction.positive_float_error x hxf hx hxpos
  rw [hsv] at hYe
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  have hH := ExpCoreRange.head_bounds j
  obtain ⟨hEn, hEz⟩ := ExpOneStep.target_bounds x.toBits hxf hx k q j hkv hk
  have hElo : (2 : ℝ) ^ q * (319 / 320) ≤ Real.exp (value x.toBits) := by
    by_cases hj0 : j.val = 0
    · exact (hEz hj0).1
    · have := (hEn hj0).1
      linarith
  let P := (2 : ℝ) ^ (1009 : Int) * value Y.toBits
  have h1009 : (2 : ℝ) ^ (1009 : Int) * (2 : ℝ) ^ (-1009 : Int) = 1 := by
    rw [← zpow_add₀ (by norm_num), show (1009 : Int) + -1009 = 0 by norm_num, zpow_zero]
  have hq1009 : (2 : ℝ) ^ (1009 : Int) * (2 : ℝ) ^ (q - 1009) = (2 : ℝ) ^ q := by
    rw [← zpow_add₀ (by norm_num), show (1009 : Int) + (q - 1009) = q by ring]
  have herr : |P - Real.exp (value x.toBits)| ≤
      (7 / 5) * unitRoundoff64 * ((2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) := by
    have hPE : P - Real.exp (value x.toBits) = (2 : ℝ) ^ (1009 : Int) *
        (value Y.toBits - (2 : ℝ) ^ (-1009 : Int) * Real.exp (value x.toBits)) := by
      rw [mul_sub, ← mul_assoc, h1009, one_mul]
    rw [hPE, abs_mul, abs_of_pos (zpow_pos (by norm_num) _)]
    calc
      _ ≤ (2 : ℝ) ^ (1009 : Int) * ((7 / 5) * unitRoundoff64 *
          ((2 : ℝ) ^ (q - 1009) * value (ExpTableBounds.headBits j.val))) :=
        mul_le_mul_of_nonneg_left hYe (by positivity)
      _ = _ := by
        rw [← hq1009]
        ring
  have hYv : 1 / (2 : ℝ) ^ 1022 < value Y.toBits := by
    have hR : (2 : ℝ) ^ (-1009 : Int) * (2 : ℝ) ^ q = (2 : ℝ) ^ (q - 1009) := by
      rw [← zpow_add₀ (by norm_num), show (-1009 : Int) + q = q - 1009 by ring]
    have hRlo : (2 : ℝ) ^ (-1000 : Int) ≤ (2 : ℝ) ^ (q - 1009) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hp1000 : (2 : ℝ) ^ (-1000 : Int) = 1 / (2 : ℝ) ^ 1000 := by norm_num
    have hm : (2 : ℝ) ^ (q - 1009) * (319 / 320) ≤
        (2 : ℝ) ^ (-1009 : Int) * Real.exp (value x.toBits) := by
      rw [← hR, mul_assoc]
      exact mul_le_mul_of_nonneg_left hElo (by positivity)
    have hHb : (2 : ℝ) ^ (q - 1009) * value (ExpTableBounds.headBits j.val) ≤
        (2 : ℝ) ^ (q - 1009) * (255 / 128) :=
      mul_le_mul_of_nonneg_left hH.1 (by positivity)
    have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
    have hYe' := (abs_le.mp hYe).1
    rw [hu] at hYe'
    have h1022 : (1 : ℝ) / 2 ^ 1022 < 1 / 2 ^ 1000 / 2 := by norm_num
    nlinarith
  obtain ⟨hYe1, hYs⟩ := normal_of_value Y.toBits hYv
  have hword := scale_up_word
  have hsum : 1024 ≤ Wasm.IEEE64.exponent Y.toBits + 2032 := by omega
  have hc : ((Exp.exp x).toBits.toNat < limit ∧ value (Exp.exp x).toBits = P) ∨
      ((Exp.exp x).toBits = F64PositiveRounding.positiveInfinity ∧ (2 : ℝ) ^ 1024 ≤ P) := by
    rw [hexp, hword]
    by_cases hov : 0x7FF ≤ Wasm.IEEE64.exponent Y.toBits + 2032 - 1023
    · right
      rw [F64PowerScale.mul_power_overflow 2032 Y.toBits (by norm_num) (by norm_num) hYf hYe1
        hsum hov, hYs, infinity_word]
      refine ⟨rfl, ?_⟩
      have hv := value_ge_of_exponent Y.toBits 1038 15 (by norm_num) (by norm_num) (by norm_num)
        hYs (by omega)
      have hp : (2 : ℝ) ^ (1009 : Int) * (2 : ℝ) ^ (15 : Int) = (2 : ℝ) ^ 1024 := by
        rw [← zpow_add₀ (by norm_num), show (1009 : Int) + 15 = ((1024 : Nat) : Int) by norm_num,
          zpow_natCast]
      calc
        (2 : ℝ) ^ 1024 = (2 : ℝ) ^ (1009 : Int) * (2 : ℝ) ^ (15 : Int) := hp.symm
        _ ≤ P := mul_le_mul_of_nonneg_left hv (by positivity)
    · left
      obtain ⟨hcf, hcv⟩ := F64PowerScale.mul_power_finite 2032 Y.toBits (by norm_num)
        (by norm_num) hYf hYe1 hsum (by omega)
      have hcv' : value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false 2032 0) Y.toBits) = P := by
        rw [hcv, show ((2032 : Nat) : Int) - 1023 = 1009 by norm_num]
      refine ⟨F64PositiveOrder.positive_finite_encoding _ hcf ?_, hcv'⟩
      rw [hcv']
      have : (0 : ℝ) < 1 / (2 : ℝ) ^ 1022 := by positivity
      exact mul_pos (zpow_pos (by norm_num) _) (this.trans hYv)
  have hlim : (Exp.exp x).toBits.toNat ≤ limit := by
    rcases hc with ⟨h, _⟩ | ⟨h, _⟩
    · exact h.le
    · rw [h]
      decide
  exact ⟨hlim, ExpOneStep.one_step_of_error (Real.exp (value x.toBits)) P (Exp.exp x).toBits q j
    (by omega) hEn hEz herr hc⟩

#print axioms scale_up_word
#print axioms infinity_word
#print axioms normal_of_value
#print axioms value_ge_of_exponent
#print axioms positive_one_step

end Verified.Examples.ExpSpecialPositive
