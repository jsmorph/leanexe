import Project.Gelu.Tail

namespace Project.GeluWide

theorem argument_lower (a : ℝ) (ha : 8 ≤ a) : 6*a ≤ Gelu.Real.argument a := by
  have hp : 0 ≤ a := by linarith
  have hs : 79/100 ≤ Gelu.Real.scale := by linarith [Gelu.Real.scale_bounds.1]
  have hc : 19/5 ≤ 1+Gelu.Real.coefficient*a^2 := by
    have ha2 : 64 ≤ a^2 := by nlinarith
    norm_num [Gelu.Real.coefficient] at *
    linarith
  have hfactor : 6 ≤ 2*Gelu.Real.scale*(1+Gelu.Real.coefficient*a^2) := by
    have hh := mul_le_mul (show 79/50 ≤ 2*Gelu.Real.scale by linarith) hc
      (by norm_num : (0:ℝ) ≤ 19/5) (by linarith : 0 ≤ 2*Gelu.Real.scale)
    linarith
  have hh := mul_le_mul_of_nonneg_right hfactor hp
  unfold Gelu.Real.argument
  nlinarith only [hh]

theorem exp_fortyEight_lower : (10:ℝ)^20 ≤ Real.exp 48 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) h1 48
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith only [hp]

theorem argument_exp_lower (a : ℝ) (ha : 8 ≤ a) :
    10^18*a ≤ Real.exp (Gelu.Real.argument a) := by
  have he := Real.add_one_le_exp (6*a-48)
  have hx : 0 ≤ 6*a-47 := by linarith
  have hh := mul_le_mul exp_fortyEight_lower (show 6*a-47 ≤ Real.exp (6*a-48) by linarith)
    hx (Real.exp_pos 48).le
  rw [← Real.exp_add, show (48:ℝ)+(6*a-48) = 6*a by ring] at hh
  have hu := Real.exp_le_exp.mpr (argument_lower a ha)
  linarith

theorem positive_tail (a : ℝ) (ha : 8 ≤ a) : |Gelu.Real.gelu a-a| ≤ 1/10^18 := by
  rw [← Gelu.Real.gelu_neg, Gelu.Real.gelu_logistic, Gelu.Real.argument_neg, neg_neg]
  rw [abs_div, abs_neg, abs_of_nonneg (by linarith : 0 ≤ a),
    abs_of_pos (by positivity : 0 < 1+Real.exp (Gelu.Real.argument a))]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith [argument_exp_lower a ha]

theorem negative_tail (a : ℝ) (ha : a ≤ -8) : |Gelu.Real.gelu a| ≤ 1/10^18 := by
  have hh := positive_tail (-a) (by linarith)
  rw [Gelu.Real.gelu_neg] at hh
  simpa only [sub_neg_eq_add, sub_add_cancel] using hh

#print axioms positive_tail
#print axioms negative_tail
end Project.GeluWide
