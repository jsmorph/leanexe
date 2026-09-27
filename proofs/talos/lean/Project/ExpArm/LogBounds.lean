import Project.ProofKit.F64Rational
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit.F64Rational

def log2Series : ℚ := ∑ i ∈ Finset.range 110, (1/2 : ℚ)^(i+1)/(i+1)

theorem split_log_rational :
    |decode 0xBF762E42FEFA0000 + decode 0xBD0CF79ABC9E3B3A + log2Series/128| +
      1/(2 : ℚ)^117 ≤ 1/(2 : ℚ)^100 := by
  decide +kernel

theorem log2_series_error : |(log2Series : ℝ) - Real.log 2| ≤ 1/(2 : ℝ)^110 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/2 : ℝ)) (by norm_num) 110
  simp only [abs_of_pos (by norm_num : (0 : ℝ) < 1/2),
    show (1 - (1/2 : ℝ)) = 2⁻¹ by norm_num, Real.log_inv] at h
  rw [← sub_eq_add_neg] at h
  have he : (log2Series : ℝ) =
      ∑ i ∈ Finset.range 110, (1/2 : ℝ)^(i+1)/(i+1) := by
    simp only [log2Series, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
      Rat.cast_one, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast]
  rw [he]
  convert h using 1
  norm_num

theorem log2_quotient_error : |(Real.log 2 - (log2Series : ℝ))/128| ≤ 1/(2 : ℝ)^117 := by
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 128), abs_sub_comm]
  calc
    _ ≤ (1/(2 : ℝ)^110)/128 := div_le_div_of_nonneg_right log2_series_error (by norm_num)
    _ = _ := by norm_num

theorem split_log_error :
    |value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + Real.log 2/128| ≤
      1/(2 : ℝ)^100 := by
  have hc : ((|decode 0xBF762E42FEFA0000 + decode 0xBD0CF79ABC9E3B3A + log2Series/128| +
      1/(2 : ℚ)^117 : ℚ) : ℝ) ≤ ((1/(2 : ℚ)^100 : ℚ) : ℝ) :=
    Rat.cast_le.mpr split_log_rational
  push_cast at hc
  simp only [decode_cast] at hc
  have ht := abs_add_le
    (value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + (log2Series : ℝ)/128)
    ((Real.log 2 - (log2Series : ℝ))/128)
  have hs : value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + (log2Series : ℝ)/128 +
      (Real.log 2 - (log2Series : ℝ))/128 =
      value 0xBF762E42FEFA0000 + value 0xBD0CF79ABC9E3B3A + Real.log 2/128 := by ring
  rw [hs] at ht
  exact ht.trans ((add_le_add le_rfl log2_quotient_error).trans hc)

theorem inverse_log_rational :
    |decode 0x40671547652B82FE * log2Series/128 - 1| +
      |decode 0x40671547652B82FE|/(2 : ℚ)^117 ≤ 1/(2 : ℚ)^55 := by
  decide +kernel

theorem inverse_log_error : |value 0x40671547652B82FE * (Real.log 2/128) - 1| ≤
    1/(2 : ℝ)^55 := by
  have hc : ((|decode 0x40671547652B82FE * log2Series/128 - 1| +
      |decode 0x40671547652B82FE|/(2 : ℚ)^117 : ℚ) : ℝ) ≤ ((1/(2 : ℚ)^55 : ℚ) : ℝ) :=
    Rat.cast_le.mpr inverse_log_rational
  push_cast at hc
  simp only [decode_cast] at hc
  have ht := abs_add_le
    (value 0x40671547652B82FE * (log2Series : ℝ)/128 - 1)
    (value 0x40671547652B82FE * ((Real.log 2 - (log2Series : ℝ))/128))
  have hd : |value 0x40671547652B82FE * ((Real.log 2 - (log2Series : ℝ))/128)| ≤
      |value 0x40671547652B82FE|/(2 : ℝ)^117 := by
    rw [abs_mul]
    calc
      _ ≤ |value 0x40671547652B82FE| * (1/(2 : ℝ)^117) :=
        mul_le_mul_of_nonneg_left log2_quotient_error (abs_nonneg _)
      _ = _ := by ring
  have hs : value 0x40671547652B82FE * (log2Series : ℝ)/128 - 1 +
      value 0x40671547652B82FE * ((Real.log 2 - (log2Series : ℝ))/128) =
      value 0x40671547652B82FE * (Real.log 2/128) - 1 := by ring
  rw [hs] at ht
  exact ht.trans ((add_le_add le_rfl hd).trans hc)

#print axioms split_log_error
#print axioms inverse_log_error
end Project.ExpArm
