import Library.Numerics.Float64.Exp.ExpResidualFloat
import Library.Numerics.Float64.Exp.ExpReconstructionBounds

namespace Library.Numerics.Float64.Exp.ExpReducedReconstruction
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- Replacing the computed residual by the ideal one changes `s (1 + t) exp r` by at most
`s / 2 ^ 58`. -/
theorem residual_change (x s t : UInt64)
    (hxf : Finite x) (hx : |value x| ≤ 768) (hS : 0 < value s)
    (ht : |value t| ≤ 1 / (2 : ℝ) ^ 53) :
    |value s * (1 + value t) * Real.exp (value (ExpResidualBounds.residual x)) -
      value s * (1 + value t) * Real.exp (ExpResidualBounds.ideal x)| ≤
      value s * (1 / (2 : ℝ) ^ 58) := by
  have hr := ExpResidualBounds.residual_bounds x hxf hx
  have hi := ExpResidualBounds.ideal_bound x hxf hx
  have htail : |1 + value t| ≤ 2 := by
    calc
      _ ≤ |(1 : ℝ)| + |value t| := abs_add_le _ _
      _ ≤ 1 + 1 / (2 : ℝ) ^ 53 := by
        simpa only [abs_one] using add_le_add (le_refl (1 : ℝ)) ht
      _ ≤ 2 := by norm_num
  have hp := RealExpError.exp_perturbation_small (ExpResidualBounds.ideal x)
    (value (ExpResidualBounds.residual x)) (hi.trans (by norm_num))
    (hr.2.2.trans (by norm_num))
  have hexp :
      |Real.exp (value (ExpResidualBounds.residual x)) -
        Real.exp (ExpResidualBounds.ideal x)| ≤ 1 / (2 : ℝ) ^ 59 :=
    (hp.trans (mul_le_mul_of_nonneg_left hr.2.2 (by norm_num))).trans (by norm_num)
  rw [show value s * (1 + value t) * Real.exp (value (ExpResidualBounds.residual x)) -
    value s * (1 + value t) * Real.exp (ExpResidualBounds.ideal x) =
    value s * (1 + value t) *
      (Real.exp (value (ExpResidualBounds.residual x)) -
        Real.exp (ExpResidualBounds.ideal x)) by ring]
  rw [abs_mul, abs_mul, abs_of_pos hS]
  calc
    _ ≤ (value s * 2) * (1 / (2 : ℝ) ^ 59) :=
      mul_le_mul (mul_le_mul_of_nonneg_left htail hS.le) hexp (abs_nonneg _)
        (by positivity)
    _ = _ := by norm_num; ring

theorem reconstruction_ideal_error (x s t : UInt64)
    (hxf : Finite x) (hx : |value x| ≤ 768) (hsf : Finite s) (htf : Finite t)
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000)
    (ht : |value t| ≤ 1 / (2 : ℝ) ^ 53) :
    Finite (ExpReconstructionBounds.reconstruction s (ExpResidualBounds.residual x) t) ∧
      |value (ExpReconstructionBounds.reconstruction s (ExpResidualBounds.residual x) t) -
        value s * (1 + value t) * Real.exp (ExpResidualBounds.ideal x)| ≤
        (11 / 8) * unitRoundoff64 * value s := by
  have hr := ExpResidualBounds.residual_bounds x hxf hx
  have he := ExpReconstructionBounds.reconstruction_error s (ExpResidualBounds.residual x) t
    hsf hr.1 htf hslo hshi hr.2.1 ht
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  have hbetween := residual_change x s t hxf hx hS ht
  refine ⟨he.1, ?_⟩
  calc
    _ ≤ (4 / 3) * unitRoundoff64 * value s + value s * (1 / (2 : ℝ) ^ 58) :=
      (abs_sub_le _ (value s * (1 + value t) *
        Real.exp (value (ExpResidualBounds.residual x))) _).trans (add_le_add he.2 hbetween)
    _ = (131 / 96) * unitRoundoff64 * value s := by norm_num [unitRoundoff64]; ring
    _ ≤ (11 / 8) * unitRoundoff64 * value s :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (131 / 96 : ℝ) ≤ 11 / 8)
          (by norm_num [unitRoundoff64])) hS.le

#print axioms residual_change
#print axioms reconstruction_ideal_error

end Library.Numerics.Float64.Exp.ExpReducedReconstruction
