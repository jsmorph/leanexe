import Project.Gelu.Real

namespace Project.Gelu.Real

theorem argument_neg (x : ℝ) : argument (-x) = -argument x := by
  unfold argument
  ring

theorem argument_nonnegative (x : ℝ) (hx : 0 ≤ x) : 0 ≤ argument x := by
  have hk : 0 ≤ scale := Real.sqrt_nonneg _
  have hc : 0 ≤ coefficient := by norm_num [coefficient]
  unfold argument
  positivity

theorem argument_lower (a : ℝ) (ha : 3 ≤ a) : 2*a ≤ argument a := by
  have hp : 0 ≤ a := by linarith
  have hs : 3/4 ≤ scale := by linarith [scale_bounds.1]
  have hc : 7/5 ≤ 1+coefficient*a^2 := by
    have ha2 : 9 ≤ a^2 := by nlinarith
    norm_num [coefficient] at *
    linarith
  have hfactor : 2 ≤ 2*scale*(1+coefficient*a^2) := by
    have h := mul_le_mul (show 3/2 ≤ 2*scale by linarith) hc
      (by norm_num : (0:ℝ) ≤ 7/5) (by linarith : 0 ≤ 2*scale)
    linarith
  have h := mul_le_mul_of_nonneg_right hfactor hp
  unfold argument
  nlinarith only [h]

theorem exp_six_lower : (300:ℝ) ≤ Real.exp 6 := by
  have h := Real.sum_le_exp_of_nonneg (x := 6) (by norm_num) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem argument_exp_lower (a : ℝ) (ha : 3 ≤ a) : 100*a ≤ Real.exp (argument a) := by
  have he := Real.add_one_le_exp (2*a-6)
  have hx : 0 ≤ 2*a-5 := by linarith
  have h := mul_le_mul exp_six_lower (show 2*a-5 ≤ Real.exp (2*a-6) by linarith)
    hx (Real.exp_pos 6).le
  rw [← Real.exp_add, show (6:ℝ)+(2*a-6) = 2*a by ring] at h
  have hu := Real.exp_le_exp.mpr (argument_lower a ha)
  linarith

theorem positive_tail (a : ℝ) (ha : 3 ≤ a) : |gelu a-a| ≤ 1/100 := by
  rw [← gelu_neg, gelu_logistic, argument_neg, neg_neg]
  rw [abs_div, abs_neg, abs_of_nonneg (by linarith : 0 ≤ a),
    abs_of_pos (by positivity : 0 < 1+Real.exp (argument a))]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith [argument_exp_lower a ha]

theorem negative_tail (a : ℝ) (ha : a ≤ -3) : |gelu a| ≤ 1/100 := by
  have h := positive_tail (-a) (by linarith)
  rw [gelu_neg] at h
  simpa only [sub_neg_eq_add, sub_add_cancel] using h

#print axioms positive_tail
#print axioms negative_tail
end Project.Gelu.Real
