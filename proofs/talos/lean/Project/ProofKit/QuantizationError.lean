import Mathlib.Tactic

namespace Project.ProofKit.QuantizationError

theorem reconstruction_error (x scale quotient clipped rounded quotientError clipError roundError : ℝ)
    (hs : 0 < scale)
    (hq : |quotient - x / scale| ≤ quotientError)
    (hc : |clipped - quotient| ≤ clipError)
    (hr : |rounded - clipped| ≤ roundError) :
    |scale * rounded - x| ≤ scale * (roundError + clipError + quotientError) := by
  have hsum : |rounded - x / scale| ≤ roundError + clipError + quotientError := by
    calc
      |rounded - x / scale| = |(rounded - clipped) + (clipped - quotient) + (quotient - x / scale)| := by
        congr 1
        ring
      _ ≤ |rounded - clipped| + |clipped - quotient| + |quotient - x / scale| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ roundError + clipError + quotientError := add_le_add (add_le_add hr hc) hq
  have heq : scale * rounded - x = scale * (rounded - x / scale) := by
    field_simp [ne_of_gt hs]
  rw [heq, abs_mul, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left hsum hs.le

theorem product_error (x w qx qw dx dw : ℝ)
    (hx : |qx - x| ≤ dx) (hw : |qw - w| ≤ dw) :
    |qx * qw - x * w| ≤ |w| * dx + |x| * dw + dx * dw := by
  have hdx : 0 ≤ dx := (abs_nonneg _).trans hx
  calc
    |qx * qw - x * w| = |w * (qx - x) + x * (qw - w) + (qx - x) * (qw - w)| := by
      congr 1
      ring
    _ ≤ |w| * |qx - x| + |x| * |qw - w| + |qx - x| * |qw - w| := by
      simpa only [abs_mul] using
        (abs_add_le (w * (qx - x) + x * (qw - w)) ((qx - x) * (qw - w))).trans
          (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |w| * dx + |x| * dw + dx * dw :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hw (abs_nonneg _)))
        (mul_le_mul hx hw (abs_nonneg _) hdx)

theorem dot_error {ι : Type*} (indices : Finset ι) (x w qx qw dx dw : ι → ℝ)
    (hx : ∀ i ∈ indices, |qx i - x i| ≤ dx i)
    (hw : ∀ i ∈ indices, |qw i - w i| ≤ dw i) :
    |(∑ i ∈ indices, qx i * qw i) - ∑ i ∈ indices, x i * w i| ≤
      ∑ i ∈ indices, (|w i| * dx i + |x i| * dw i + dx i * dw i) := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i hi => product_error _ _ _ _ _ _ (hx i hi) (hw i hi)))

theorem preserves_unique_maximum {ι : Type*} (reference quantized errors : ι → ℝ) (winner : ι)
    (he : ∀ i, |quantized i - reference i| ≤ errors i)
    (hm : ∀ i, i ≠ winner → reference winner - reference i > errors winner + errors i) :
    ∀ i, i ≠ winner → quantized winner > quantized i := by
  intro i hi
  have hw := abs_le.mp (he winner)
  have hj := abs_le.mp (he i)
  have hmargin := hm i hi
  linarith

theorem preserves_unique_maximum_uniform {ι : Type*}
    (reference quantized : ι → ℝ) (error : ℝ) (winner : ι)
    (he : ∀ i, |quantized i - reference i| ≤ error)
    (hm : ∀ i, i ≠ winner → reference winner - reference i > 2 * error) :
    ∀ i, i ≠ winner → quantized winner > quantized i := by
  apply preserves_unique_maximum reference quantized (fun _ => error) winner he
  intro i hi
  simpa only [two_mul] using hm i hi

#print axioms reconstruction_error
#print axioms dot_error
#print axioms preserves_unique_maximum

end Project.ProofKit.QuantizationError
