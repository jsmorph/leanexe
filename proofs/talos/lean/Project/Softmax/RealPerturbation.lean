import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Project.Softmax.Real

noncomputable def weight {ι : Type} (visible : ι → Bool) (s : ι → ℝ) (i : ι) : ℝ :=
  if visible i then Real.exp (s i) else 0

noncomputable def probability {ι : Type} [Fintype ι]
    (visible : ι → Bool) (s : ι → ℝ) (i : ι) : ℝ :=
  weight visible s i / ∑ j, weight visible s j

theorem weight_nonnegative {ι : Type} (visible : ι → Bool) (s : ι → ℝ) (i : ι) :
    0 ≤ weight visible s i := by
  unfold weight
  split <;> positivity

theorem weight_sum_positive {ι : Type} [Fintype ι]
    (visible : ι → Bool) (s : ι → ℝ) (h : ∃ i, visible i = true) :
    0 < ∑ i, weight visible s i := by
  obtain ⟨i, hi⟩ := h
  apply lt_of_lt_of_le (b := weight visible s i)
  · simp [weight, hi, Real.exp_pos]
  · exact Finset.single_le_sum (fun j _ => weight_nonnegative visible s j) (Finset.mem_univ i)

theorem quotient_slope_bound {ι : Type} [Fintype ι]
    (w v : ι → ℝ) (delta : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : 0 < ∑ i, w i) (hd : 0 ≤ delta) (hv : ∀ i, |v i| ≤ delta*w i) (i : ι) :
    |(v i*(∑ j, w j)-w i*(∑ j, v j))/(∑ j, w j)^2| ≤ 2*delta := by
  have hsum : |∑ j, v j| ≤ delta*(∑ j, w j) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun j _ => hv j)).trans (by rw [Finset.mul_sum]))
  have hi : w i ≤ ∑ j, w j :=
    Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  have h1 : |v i*(∑ j, w j)| ≤ delta*w i*(∑ j, w j) := by
    rw [abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_right (hv i) hs.le
  have h2 : |w i*(∑ j, v j)| ≤ w i*(delta*(∑ j, w j)) := by
    rw [abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_mul_of_nonneg_left hsum (hw i)
  have hnum := (abs_sub _ _).trans (add_le_add h1 h2)
  rw [abs_div, abs_of_pos (sq_pos_of_pos hs)]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  have hm := mul_le_mul_of_nonneg_right hi (mul_nonneg hd hs.le)
  nlinarith only [hnum, hm]

theorem weight_derivative {ι : Type} (visible : ι → Bool) (x d : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun u => weight visible (fun j => x j+u*d j) i)
      (weight visible (fun j => x j+t*d j) i*d i) t := by
  unfold weight
  split
  · convert (((hasDerivAt_id t).mul_const (d i)).const_add (x i)).exp using 1 <;>
      first | rfl | simp
  · simpa using hasDerivAt_const t (0 : ℝ)

theorem probability_derivative {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x d : ι → ℝ) (i : ι) (t : ℝ)
    (h : ∃ j, visible j = true) :
    let w := weight visible (fun j => x j+t*d j)
    HasDerivAt (fun u => probability visible (fun j => x j+u*d j) i)
      ((w i*d i*(∑ j, w j)-w i*(∑ j, w j*d j))/(∑ j, w j)^2) t := by
  dsimp only
  exact (weight_derivative visible x d i t).div
    (HasDerivAt.fun_sum (fun j _ => weight_derivative visible x d j t))
    (ne_of_gt (weight_sum_positive visible _ h))

theorem probability_perturbation {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x y : ι → ℝ) (delta : ℝ)
    (h : ∃ j, visible j = true) (hd : 0 ≤ delta)
    (he : ∀ j, |x j-y j| ≤ delta) (i : ι) :
    |probability visible x i-probability visible y i| ≤ 2*delta := by
  let d := fun j => y j-x j
  let w := fun t => weight visible (fun j => x j+t*d j)
  have hder (t : ℝ) := probability_derivative visible x d i t h
  have hbound (t : ℝ) :
      |(w t i*d i*(∑ j, w t j)-w t i*(∑ j, w t j*d j))/(∑ j, w t j)^2| ≤ 2*delta := by
    apply quotient_slope_bound (w t) (fun j => w t j*d j) delta
      (weight_nonnegative visible _) (weight_sum_positive visible _ h) hd
    intro j
    rw [abs_mul, abs_of_nonneg (weight_nonnegative visible _ j)]
    have hh : |d j| ≤ delta := by dsimp [d]; rw [abs_sub_comm]; exact he j
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (weight_nonnegative visible _ j)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t (_ : t ∈ Set.Icc 0 1) => (hder t).hasDerivWithinAt)
    (fun t (_ : t ∈ Set.Ico 0 1) => by simpa only [Real.norm_eq_abs] using hbound t)
  simpa only [Real.norm_eq_abs, d, one_mul, zero_mul, add_zero, add_sub_cancel,
    abs_sub_comm] using hh

#print axioms probability_perturbation
end Project.Softmax.Real
