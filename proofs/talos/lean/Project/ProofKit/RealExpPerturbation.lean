import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Project.ProofKit.RealExpPerturbation

theorem nonpositive (x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  let f := fun t : ℝ => Real.exp (x + t * (y - x))
  have hDerivative (t : ℝ) : HasDerivAt f (Real.exp (x + t * (y - x)) * (y - x)) t := by
    simpa only [f, id_eq, one_mul] using (((hasDerivAt_id t).mul_const (y - x)).const_add x).exp
  have hBound (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
      ‖Real.exp (x + t * (y - x)) * (y - x)‖ ≤ |x - y| := by
    have hPoint : x + t * (y - x) ≤ 0 := by
      have h1 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 - t by linarith [ht.2]) hx
      have h2 := mul_nonpos_of_nonneg_of_nonpos ht.1 hy
      nlinarith only [h1, h2]
    have hExp : Real.exp (x + t * (y - x)) ≤ 1 := Real.exp_le_one_iff.mpr hPoint
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm y x]
    exact (mul_le_mul_of_nonneg_right hExp (abs_nonneg _)).trans_eq (one_mul _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t (_ : t ∈ Set.Icc 0 1) => (hDerivative t).hasDerivWithinAt) hBound
  simpa only [f, Real.norm_eq_abs, zero_mul, one_mul, add_zero, add_sub_cancel, abs_sub_comm] using h

#print axioms nonpositive
end Project.ProofKit.RealExpPerturbation
