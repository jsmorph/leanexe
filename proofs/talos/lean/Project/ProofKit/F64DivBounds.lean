import Project.ProofKit.F64RationalBounds
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64DivBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem abs_scaledValue_real (a : UInt64) :
    |(Wasm.IEEE64.scaledValue a : ℝ)| = (Wasm.IEEE64.scaledMagnitude a : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs, natAbs_scaledValue]
  norm_num

theorem quotient_abs_scaled (a b : UInt64) :
    |value a / value b| =
      (Wasm.IEEE64.scaledMagnitude a : ℝ) / Wasm.IEEE64.scaledMagnitude b := by
  simp [value, abs_div, abs_scaledValue_real]
  exact div_div_div_cancel_right₀ (by positivity) _ _

theorem div_scaled_adaptive (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hbound : Wasm.IEEE64.scaledMagnitude a * 2^1074 <
      Wasm.IEEE64.scaledMagnitude b * 2^2096) :
    Finite (Wasm.IEEE64.div a b) ∧
    |Wasm.IEEE64.scaledValue (Wasm.IEEE64.div a b) * Wasm.IEEE64.scaledValue b -
      Wasm.IEEE64.scaledValue a * (2 : Int)^1074| * (2^53 : Int) ≤
      (max (Wasm.IEEE64.scaledMagnitude a * 2^1074)
        (Wasm.IEEE64.scaledMagnitude b * 2^52) : Nat) := by
  let numerator := Wasm.IEEE64.scaledMagnitude a * 2^1074
  let denominator := Wasm.IEEE64.scaledMagnitude b
  have hs := F64RationalBounds.rational_relative
    (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) numerator denominator hb0 hbound
  rw [div_finite_rounder a b ha hb hb0]
  refine ⟨hs.1, ?_⟩
  have herr := hs.2.2
  have hresultSign := hs.2.1
  have habs (x y : Int) : |-x + y| = |x + -y| := by
    rw [show -x + y = -(x + -y) by ring, abs_neg]
  cases hsa : Wasm.IEEE64.sign a <;>
    cases hsb : Wasm.IEEE64.sign b <;>
    simp [numerator, denominator, hsa, hsb] at hresultSign <;>
    simp [Wasm.IEEE64.scaledValue, hresultSign, hsa, hsb, numerator, denominator] at herr ⊢
  all_goals
    first
    | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
    | rw [habs]
      simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr

theorem div_real_mixed (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hbound : |value a / value b| < (2 : ℝ)^1022) :
    Finite (Wasm.IEEE64.div a b) ∧
    |value (Wasm.IEEE64.div a b) - value a / value b| ≤
      unitRoundoff64 * |value a / value b| + multiplicationUnderflowEpsilon := by
  have hbMagPos : (0 : ℝ) < Wasm.IEEE64.scaledMagnitude b := by
    exact_mod_cast Nat.pos_of_ne_zero hb0
  have hscaledBound : Wasm.IEEE64.scaledMagnitude a * 2^1074 <
      Wasm.IEEE64.scaledMagnitude b * 2^2096 := by
    rw [quotient_abs_scaled] at hbound
    have h := (div_lt_iff₀ hbMagPos).mp hbound
    have hm := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < (2 : ℝ)^1074)
    have heq : (2 : ℝ)^1022 * Wasm.IEEE64.scaledMagnitude b * (2 : ℝ)^1074 =
        Wasm.IEEE64.scaledMagnitude b * (2 : ℝ)^2096 := by
      rw [mul_comm ((2 : ℝ)^1022), mul_assoc, ← pow_add]
    rw [heq] at hm
    exact_mod_cast hm
  have hs := div_scaled_adaptive a b ha hb hb0 hscaledBound
  refine ⟨hs.1, ?_⟩
  let z : Int := Wasm.IEEE64.scaledValue (Wasm.IEEE64.div a b) *
    Wasm.IEEE64.scaledValue b - Wasm.IEEE64.scaledValue a * (2 : Int)^1074
  have hz : |z| * (2^53 : Int) ≤
      (max (Wasm.IEEE64.scaledMagnitude a * 2^1074)
        (Wasm.IEEE64.scaledMagnitude b * 2^52) : Nat) := hs.2
  have hzReal : |(z : ℝ)| * (2 : ℝ)^53 ≤
      max ((Wasm.IEEE64.scaledMagnitude a : ℝ) * (2 : ℝ)^1074)
        ((Wasm.IEEE64.scaledMagnitude b : ℝ) * (2 : ℝ)^52) := by
    exact_mod_cast hz
  have hbScaledReal : (Wasm.IEEE64.scaledValue b : ℝ) ≠ 0 := by
    have h := abs_scaledValue_real b
    intro hz
    rw [hz, abs_zero] at h
    linarith
  have heq : value (Wasm.IEEE64.div a b) - value a / value b =
      (z : ℝ) / ((2 : ℝ)^1074 * Wasm.IEEE64.scaledValue b) := by
    simp [value, z]
    field_simp
    ring
  rw [heq, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) hbScaledReal))).2
  apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < (2 : ℝ)^53)).mp
  calc
    |(z : ℝ)| * (2 : ℝ)^53 ≤
        (Wasm.IEEE64.scaledMagnitude a : ℝ) * (2 : ℝ)^1074 +
          (Wasm.IEEE64.scaledMagnitude b : ℝ) * (2 : ℝ)^52 :=
      hzReal.trans (max_le (le_add_of_nonneg_right (by positivity))
        (le_add_of_nonneg_left (by positivity)))
    _ = (unitRoundoff64 * |value a / value b| + multiplicationUnderflowEpsilon) *
        |(2 : ℝ)^1074 * Wasm.IEEE64.scaledValue b| * (2 : ℝ)^53 := by
      rw [quotient_abs_scaled, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)^1074),
        abs_scaledValue_real]
      norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
      field_simp
      ring

#print axioms div_scaled_adaptive
#print axioms div_real_mixed
end Project.ProofKit.F64DivBounds
