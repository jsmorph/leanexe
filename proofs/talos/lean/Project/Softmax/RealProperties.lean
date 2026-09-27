import Project.Softmax.RealPerturbation

namespace Project.Softmax.Real

theorem probability_congr_visible {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x y : ι → ℝ)
    (h : ∀ j, visible j = true → x j = y j) (i : ι) :
    probability visible x i = probability visible y i := by
  have hw : weight visible x = weight visible y := by
    funext j
    unfold weight
    split
    · rename_i hj
      rw [h j hj]
    · rfl
  simp only [probability, hw]

theorem probability_zero {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x : ι → ℝ) (i : ι) (h : visible i = false) :
    probability visible x i = 0 := by
  simp [probability, weight, h]

theorem probability_nonnegative {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x : ι → ℝ) (i : ι) :
    0 ≤ probability visible x i := by
  exact div_nonneg (weight_nonnegative visible x i)
    (Finset.sum_nonneg (fun j _ => weight_nonnegative visible x j))

theorem probability_sum {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x : ι → ℝ) (h : ∃ j, visible j = true) :
    ∑ i, probability visible x i = 1 := by
  simp only [probability, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  exact div_self (ne_of_gt (weight_sum_positive visible x h))

theorem weighted_magnitude {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x v : ι → ℝ) (bound : ℝ)
    (hv : ∀ j, visible j = true → |v j| ≤ bound)
    (h : ∃ j, visible j = true) :
    |∑ j, probability visible x j*v j| ≤ bound := by
  have hi (j : ι) : |probability visible x j*v j| ≤ probability visible x j*bound := by
    by_cases hj : visible j = true
    · rw [abs_mul, abs_of_nonneg (probability_nonnegative visible x j)]
      exact mul_le_mul_of_nonneg_left (hv j hj) (probability_nonnegative visible x j)
    · have hh : visible j = false := Bool.eq_false_iff.mpr hj
      simp [probability_zero visible x j hh]
  calc
    _ ≤ ∑ j, |probability visible x j*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, probability visible x j*bound := Finset.sum_le_sum (fun j _ => hi j)
    _ = bound := by rw [← Finset.sum_mul, probability_sum visible x h, one_mul]

end Project.Softmax.Real
