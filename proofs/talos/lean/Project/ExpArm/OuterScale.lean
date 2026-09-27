import Project.ExpArm.SubnormalAccuracy
import Project.ExpArm.ReductionBounds
import Project.ExpArm.ReconstructionBounds

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem full_correction_bounds (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 1024) :
    Finite (pathCorrection x) ∧ |value (pathCorrection x)| ≤ 1/250 := by
  let i := (reductionWord x &&& 127).toNat
  have hi : i < 128 := by
    have h : i ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    omega
  have ht := table_real_bounds i hi
  have hr := reduced_word_bound x hf hx
  have hc := correction_rounding (reducedWord x) table[2*i]! hr.1 ht.2.1 hr.2 ht.2.2.2.2
  exact ⟨hc.finite, hc.magnitude.trans (by norm_num)⟩

theorem positive_outer_integer (x : UInt64) (hf : Finite x)
    (hx : 800 ≤ value x ∧ value x ≤ 1024) :
    1149 ≤ reductionInteger x/128 ∧ reductionInteger x/128 ≤ 1480 := by
  have habs : |value x| ≤ 1024 := abs_le.mpr ⟨by linarith, hx.2⟩
  have hs := abs_le.mp (integer_selection x hf habs).2.2.2.2
  have hi := inverse_log_bounds
  have hl : (147072 : ℝ) ≤ (reductionInteger x : ℝ) := by nlinarith
  have hu : (reductionInteger x : ℝ) ≤ 189441 := by nlinarith
  have hl' : (147072 : Int) ≤ reductionInteger x := by exact_mod_cast hl
  have hu' : reductionInteger x ≤ (189441 : Int) := by exact_mod_cast hu
  omega

theorem negative_outer_integer (x : UInt64) (hf : Finite x)
    (hx : -1024 ≤ value x ∧ value x ≤ -800) :
    -1481 ≤ reductionInteger x/128 ∧ reductionInteger x/128 ≤ -1150 := by
  have habs : |value x| ≤ 1024 := abs_le.mpr ⟨hx.1, by linarith⟩
  have hs := abs_le.mp (integer_selection x hf habs).2.2.2.2
  have hi := inverse_log_bounds
  have hl : (-189441 : ℝ) ≤ (reductionInteger x : ℝ) := by nlinarith
  have hu : (reductionInteger x : ℝ) ≤ -147073 := by nlinarith
  have hl' : (-189441 : Int) ≤ reductionInteger x := by exact_mod_cast hl
  have hu' : reductionInteger x ≤ (-147073 : Int) := by exact_mod_cast hu
  omega

def positiveScale (x : UInt64) : UInt64 :=
  let word := reductionWord x
  table[2*(word &&& 127).toNat+1]! + (word <<< 45) - ((1009 : UInt64) <<< 52)

theorem positive_outer_scale (x : UInt64) (hf : Finite x)
    (hx : 800 ≤ value x ∧ value x ≤ 1024) :
    Finite (positiveScale x) ∧ (2 : ℝ)^140 ≤ value (positiveScale x) ∧
      value (positiveScale x) ≤ (2 : ℝ)^500 := by
  have hm := positive_outer_integer x hf hx
  have hs := positive_scale_value (reductionWord x) (by
    change 1 ≤ 1023+(reductionInteger x/128-1009) ∧ 1023+(reductionInteger x/128-1009) < 2047
    omega)
  have hv := scaled_table_magnitude (reductionWord x) (positiveScale x) (-1009)
    (by change 0 ≤ 1023+(reductionInteger x/128-1009); omega) hs.2.2
  change (2 : ℝ)^(reductionInteger x/128-1009) ≤ value (positiveScale x) ∧
    value (positiveScale x) ≤ (199/100)*(2 : ℝ)^(reductionInteger x/128-1009) at hv
  have hl : (2 : ℝ)^(140 : Int) ≤ (2 : ℝ)^(reductionInteger x/128-1009) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hu : (2 : ℝ)^(reductionInteger x/128-1009) ≤ (2 : ℝ)^(471 : Int) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  refine ⟨hs.1, hl.trans hv.1, ?_⟩
  have hn : (199/100)*(2 : ℝ)^(471 : Int) ≤ (2 : ℝ)^500 := by norm_num
  exact hv.2.trans ((mul_le_mul_of_nonneg_left hu (by norm_num)).trans hn)

theorem negative_outer_scale (x : UInt64) (hf : Finite x)
    (hx : -1024 ≤ value x ∧ value x ≤ -800) :
    Finite (negativeScale x) ∧ (2 : ℝ)^(-500 : Int) ≤ value (negativeScale x) ∧
      value (negativeScale x) ≤ (2 : ℝ)^(-126 : Int) := by
  have hm := negative_outer_integer x hf hx
  have hs := negative_scale_value (reductionWord x) (by
    change 1 ≤ 1023+(reductionInteger x/128+1022) ∧ 1023+(reductionInteger x/128+1022) < 2047
    omega)
  have hv := scaled_table_magnitude (reductionWord x) (negativeScale x) 1022
    (by change 0 ≤ 1023+(reductionInteger x/128+1022); omega) hs.2.2
  change (2 : ℝ)^(reductionInteger x/128+1022) ≤ value (negativeScale x) ∧
    value (negativeScale x) ≤ (199/100)*(2 : ℝ)^(reductionInteger x/128+1022) at hv
  have hl : (2 : ℝ)^(-500 : Int) ≤ (2 : ℝ)^(reductionInteger x/128+1022) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hu : (2 : ℝ)^(reductionInteger x/128+1022) ≤ (2 : ℝ)^(-128 : Int) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  refine ⟨hs.1, hl.trans hv.1, ?_⟩
  have hn : (199/100)*(2 : ℝ)^(-128 : Int) ≤ (2 : ℝ)^(-126 : Int) := by norm_num
  exact hv.2.trans ((mul_le_mul_of_nonneg_left hu (by norm_num)).trans hn)

#print axioms positive_outer_scale
#print axioms negative_outer_scale
end Project.ExpArm
