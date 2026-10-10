import CodeLib.IEEE64.Roundoff
import LeanExe.ProofKit.RealExpError
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Verified.Examples.ExpReductionBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

def splitLogTwo : ℚ :=
  128 * ((Wasm.IEEE64.scaledValue 0x3F762E42FEFA0000 : ℚ) / (2 : ℚ) ^ 1074 +
    (Wasm.IEEE64.scaledValue 0x3D0CF79ABC9E3B3A : ℚ) / (2 : ℚ) ^ 1074)

def lowerLogTwo : ℚ := splitLogTwo - 1 / (2 : ℚ) ^ 92

def upperLogTwo : ℚ := splitLogTwo + 1 / (2 : ℚ) ^ 92

def taylor (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.range 40, x ^ m / (m.factorial : ℚ)

def remainder : ℚ := 41 / ((40 : Nat).factorial * 40 : ℚ)

theorem checked_log_brackets :
    |lowerLogTwo| ≤ 1 ∧ |upperLogTwo| ≤ 1 ∧
    taylor lowerLogTwo + remainder ≤ 2 ∧
    2 ≤ taylor upperLogTwo - remainder := by
  decide +kernel

theorem taylor_error (x : ℚ) (hx : |(x : ℝ)| ≤ 1) :
    |Real.exp (x : ℝ) - (taylor x : ℝ)| ≤ (remainder : ℝ) := by
  simpa [taylor, remainder, show (40 : ℝ) + 1 = 41 by norm_num] using
    LeanExe.ProofKit.RealExpError.taylor_error_one (x : ℝ) hx 40 (by decide)

theorem log_two_enclosure :
    (lowerLogTwo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (upperLogTwo : ℝ) := by
  obtain ⟨hl, hu, htl, htu⟩ := checked_log_brackets
  have hlr : |(lowerLogTwo : ℝ)| ≤ 1 := by exact_mod_cast hl
  have hur : |(upperLogTwo : ℝ)| ≤ 1 := by exact_mod_cast hu
  have htlr : (taylor lowerLogTwo : ℝ) + (remainder : ℝ) ≤ 2 := by
    exact_mod_cast htl
  have htur : (2 : ℝ) ≤ (taylor upperLogTwo : ℝ) - (remainder : ℝ) := by
    exact_mod_cast htu
  have hel := (abs_le.mp (taylor_error lowerLogTwo hlr)).2
  have heu := (abs_le.mp (taylor_error upperLogTwo hur)).1
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  · apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mpr
    linarith

theorem split_error :
    |value 0x3F762E42FEFA0000 + value 0x3D0CF79ABC9E3B3A -
      Real.log 2 / 128| ≤ 1 / (2 : ℝ) ^ 99 := by
  have hs : (splitLogTwo : ℝ) =
      128 * (value 0x3F762E42FEFA0000 + value 0x3D0CF79ABC9E3B3A) := by
    simp [splitLogTwo, value]
  obtain ⟨hl, hu⟩ := log_two_enclosure
  simp only [lowerLogTwo, upperLogTwo, Rat.cast_sub, Rat.cast_add, Rat.cast_div,
    Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat, hs] at hl hu
  apply abs_le.mpr
  constructor <;> norm_num at hl hu ⊢ <;> linarith

#print axioms checked_log_brackets
#print axioms log_two_enclosure
#print axioms split_error


def inverseLogTwo128 : ℚ :=
  (Wasm.IEEE64.scaledValue 0x40671547652B82FE : ℚ) / (2 : ℚ) ^ 1074

theorem inverse_value_cast : (inverseLogTwo128 : ℝ) = value 0x40671547652B82FE := by
  simp [inverseLogTwo128, value]

theorem checked_inverse_bounds :
    0 < inverseLogTwo128 ∧ inverseLogTwo128 ≤ 256 ∧
    1 - 1 / (2 : ℚ) ^ 53 ≤ inverseLogTwo128 * lowerLogTwo / 128 ∧
    inverseLogTwo128 * upperLogTwo / 128 ≤ 1 + 1 / (2 : ℚ) ^ 53 := by
  decide +kernel

theorem inverse_bounds :
    0 < value 0x40671547652B82FE ∧ value 0x40671547652B82FE ≤ 256 ∧
    |value 0x40671547652B82FE * Real.log 2 / 128 - 1| ≤ 1 / (2 : ℝ) ^ 53 := by
  obtain ⟨hp, hb, hl, hu⟩ := checked_inverse_bounds
  have hpr : 0 < value 0x40671547652B82FE := by
    rw [← inverse_value_cast]
    exact_mod_cast hp
  have hbr : value 0x40671547652B82FE ≤ 256 := by
    rw [← inverse_value_cast]
    exact_mod_cast hb
  have hlr : 1 - 1 / (2 : ℝ) ^ 53 ≤
      value 0x40671547652B82FE * (lowerLogTwo : ℝ) / 128 := by
    have hc : ((1 - 1 / (2 : ℚ) ^ 53 : ℚ) : ℝ) ≤
        ((inverseLogTwo128 * lowerLogTwo / 128 : ℚ) : ℝ) := Rat.cast_le.mpr hl
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_mul, inverse_value_cast] using hc
  have hur : value 0x40671547652B82FE * (upperLogTwo : ℝ) / 128 ≤
      1 + 1 / (2 : ℝ) ^ 53 := by
    have hc : ((inverseLogTwo128 * upperLogTwo / 128 : ℚ) : ℝ) ≤
        ((1 + 1 / (2 : ℚ) ^ 53 : ℚ) : ℝ) := Rat.cast_le.mpr hu
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_mul, inverse_value_cast] using hc
  obtain ⟨hll, hul⟩ := log_two_enclosure
  have hlow := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hll hpr.le) (by norm_num : (0 : ℝ) ≤ 128)
  have hupp := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hul hpr.le) (by norm_num : (0 : ℝ) ≤ 128)
  refine ⟨hpr, hbr, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

theorem reduction_constants_finite :
    Finite 0x40671547652B82FE ∧ Finite 0x4338000000000000 ∧
    Finite 0xBF762E42FEFA0000 ∧ Finite 0xBD0CF79ABC9E3B3A := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

#print axioms checked_inverse_bounds
#print axioms inverse_bounds
#print axioms reduction_constants_finite


theorem log_two_coarse_bounds : (2 / 3 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 3 / 4 := by
  have hl : (2 / 3 : ℚ) ≤ lowerLogTwo := by decide +kernel
  have hu : upperLogTwo ≤ (3 / 4 : ℚ) := by decide +kernel
  have hlr : (2 / 3 : ℝ) ≤ (lowerLogTwo : ℝ) := by
    have hc : ((2 / 3 : ℚ) : ℝ) ≤ (lowerLogTwo : ℝ) := Rat.cast_le.mpr hl
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  have hur : (upperLogTwo : ℝ) ≤ (3 / 4 : ℝ) := by
    have hc : (upperLogTwo : ℝ) ≤ ((3 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hu
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  exact ⟨hlr.trans log_two_enclosure.1, log_two_enclosure.2.trans hur⟩

theorem inverse_upper_bound : value 0x40671547652B82FE ≤ 192 := by
  have hq : inverseLogTwo128 ≤ 192 := by decide +kernel
  have hc : (inverseLogTwo128 : ℝ) ≤ ((192 : ℚ) : ℝ) := Rat.cast_le.mpr hq
  simpa only [inverse_value_cast, Rat.cast_ofNat] using hc

#print axioms inverse_upper_bound

theorem ideal_residual_bound (x k : ℝ) (hx : |x| ≤ 1024)
    (hk : |k - value 0x40671547652B82FE * x| ≤ 1 / 2 + 1 / (2 : ℝ) ^ 34) :
    |x - k * (Real.log 2 / 128)| ≤ 1 / 320 := by
  let d := Real.log 2 / 128
  let inv := value 0x40671547652B82FE
  have hd : 0 ≤ d := by
    have hl := log_two_coarse_bounds.1
    dsimp [d]
    positivity
  have hdu : |d| ≤ (3 / 512 : ℝ) := by
    rw [abs_of_nonneg hd]
    dsimp [d]
    linarith only [log_two_coarse_bounds.2]
  have hi : |1 - inv * d| ≤ 1 / (2 : ℝ) ^ 53 := by
    rw [abs_sub_comm]
    simpa only [d, inv, mul_div_assoc, mul_one] using inverse_bounds.2.2
  calc
    _ = |x * (1 - inv * d) + (inv * x - k) * d| := by
      congr 1
      dsimp [d]
      ring
    _ ≤ |x * (1 - inv * d)| + |(inv * x - k) * d| := abs_add_le _ _
    _ = |x| * |1 - inv * d| + |inv * x - k| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ 1024 * (1 / (2 : ℝ) ^ 53) +
        (1 / 2 + 1 / (2 : ℝ) ^ 34) * (3 / 512) := by
      have hk' : |inv * x - k| ≤ 1 / 2 + 1 / (2 : ℝ) ^ 34 := by
        rw [abs_sub_comm]
        exact hk
      exact add_le_add (mul_le_mul hx hi (abs_nonneg _) (by norm_num))
        (mul_le_mul hk' hdu (abs_nonneg _) (by norm_num))
    _ ≤ 1 / 320 := by norm_num

#print axioms log_two_coarse_bounds
#print axioms ideal_residual_bound

theorem negative_low_value :
    value 0xBD0CF79ABC9E3B3A = -value 0x3D0CF79ABC9E3B3A := by
  have hs : Wasm.IEEE64.scaledValue 0xBD0CF79ABC9E3B3A =
      -Wasm.IEEE64.scaledValue 0x3D0CF79ABC9E3B3A := by decide +kernel
  simp only [value, hs, Int.cast_neg, neg_div]

theorem low_magnitude :
    |value 0xBD0CF79ABC9E3B3A| ≤ 1 / (2 : ℝ) ^ 45 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

#print axioms negative_low_value
#print axioms low_magnitude

end Verified.Examples.ExpReductionBounds
