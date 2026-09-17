import Project.Softmax.RealProperties

namespace Project.Softmax.Real

theorem weighted_quotient_slope_bound {ι : Type} [Fintype ι]
    (w d v : ι → ℝ) (delta bound : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : 0 < ∑ i, w i) (hd : 0 ≤ delta) (hb : 0 ≤ bound)
    (hdir : ∀ i, |d i| ≤ delta) (hv : ∀ i, |v i| ≤ bound) :
    |((∑ i, w i*d i*v i)*(∑ i, w i)-
      (∑ i, w i*v i)*(∑ i, w i*d i))/(∑ i, w i)^2| ≤ 2*bound*delta := by
  have hsum (c : ι → ℝ) (b : ℝ) (hc : ∀ i, |c i| ≤ b) :
      |∑ i, w i*c i| ≤ (∑ i, w i)*b := by
    calc
      _ ≤ ∑ i, |w i*c i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, w i*|c i| := by simp only [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ i, w i*b := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i) (hw i))
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hprod : |∑ i, w i*d i*v i| ≤ (∑ i, w i)*(delta*bound) := by
    simp_rw [mul_assoc]
    apply hsum
    intro i
    rw [abs_mul]
    exact mul_le_mul (hdir i) (hv i) (abs_nonneg _) hd
  have hvalues := hsum v bound hv
  have hdirection := hsum d delta hdir
  have hnum := (abs_sub _ _).trans (add_le_add
    (show |(∑ i, w i*d i*v i)*(∑ i, w i)| ≤
        (∑ i, w i)*(delta*bound)*(∑ i, w i) by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_right hprod hs.le)
    (show |(∑ i, w i*v i)*(∑ i, w i*d i)| ≤
        ((∑ i, w i)*bound)*((∑ i, w i)*delta) by
      rw [abs_mul]
      exact mul_le_mul hvalues hdirection (abs_nonneg _) (mul_nonneg hs.le hb)))
  rw [abs_div, abs_of_pos (sq_pos_of_pos hs)]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  convert hnum using 1
  ring

theorem weighted_probability_perturbation {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x y v : ι → ℝ) (delta bound : ℝ)
    (h : ∃ i, visible i = true) (hd : 0 ≤ delta) (hb : 0 ≤ bound)
    (he : ∀ i, |x i-y i| ≤ delta) (hv : ∀ i, |v i| ≤ bound) :
    |(∑ i, probability visible x i*v i)-
      (∑ i, probability visible y i*v i)| ≤ 2*bound*delta := by
  let d := fun i => y i-x i
  let w := fun t => weight visible (fun i => x i+t*d i)
  let f := fun t => (∑ i, w t i*v i)/(∑ i, w t i)
  have hder (t : ℝ) : HasDerivAt f
      (((∑ i, w t i*d i*v i)*(∑ i, w t i)-
        (∑ i, w t i*v i)*(∑ i, w t i*d i))/(∑ i, w t i)^2) t :=
    (HasDerivAt.fun_sum (fun i _ => (weight_derivative visible x d i t).mul_const (v i))).div
      (HasDerivAt.fun_sum (fun i _ => weight_derivative visible x d i t))
      (ne_of_gt (weight_sum_positive visible _ h))
  have hbound (t : ℝ) :
      |((∑ i, w t i*d i*v i)*(∑ i, w t i)-
        (∑ i, w t i*v i)*(∑ i, w t i*d i))/(∑ i, w t i)^2| ≤ 2*bound*delta := by
    apply weighted_quotient_slope_bound (w t) d v delta bound
      (weight_nonnegative visible _) (weight_sum_positive visible _ h) hd hb _ hv
    intro i
    dsimp [d]
    rw [abs_sub_comm]
    exact he i
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t (_ : t ∈ Set.Icc 0 1) => (hder t).hasDerivWithinAt)
    (fun t (_ : t ∈ Set.Ico 0 1) => by simpa only [Real.norm_eq_abs] using hbound t)
  have hx : f 0 = ∑ i, probability visible x i*v i := by
    simp only [f, w, zero_mul, add_zero, probability, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hy : f 1 = ∑ i, probability visible y i*v i := by
    simp only [f, w, d, one_mul, add_sub_cancel, probability,
      div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [Real.norm_eq_abs, hx, hy, abs_sub_comm] using hh

theorem probability_l1_perturbation {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x y : ι → ℝ) (delta : ℝ)
    (h : ∃ i, visible i = true) (hd : 0 ≤ delta)
    (he : ∀ i, |x i-y i| ≤ delta) :
    (∑ i, |probability visible x i-probability visible y i|) ≤ 2*delta := by
  let v := fun i => if 0 ≤ probability visible x i-probability visible y i then (1 : ℝ) else -1
  have hv (i : ι) : |v i| ≤ 1 := by dsimp [v]; split <;> norm_num
  have hid : (∑ i, |probability visible x i-probability visible y i|) =
      (∑ i, probability visible x i*v i)-(∑ i, probability visible y i*v i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [v]
    split_ifs with hi
    · rw [abs_of_nonneg hi]
      ring
    · rw [abs_of_neg (lt_of_not_ge hi)]
      ring
  have hh := weighted_probability_perturbation visible x y v delta 1 h hd (by norm_num) he hv
  rw [← hid, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))] at hh
  simpa only [mul_one] using hh

theorem attention_perturbation {ι : Type} [Fintype ι]
    (visible : ι → Bool) (x y v u : ι → ℝ) (scoreError valueError bound : ℝ)
    (h : ∃ i, visible i = true) (hs : 0 ≤ scoreError) (hb : 0 ≤ bound)
    (hscore : ∀ i, |x i-y i| ≤ scoreError) (hv : ∀ i, |v i| ≤ bound)
    (hvalue : ∀ i, |v i-u i| ≤ valueError) :
    |(∑ i, probability visible x i*v i)-
      (∑ i, probability visible y i*u i)| ≤ 2*bound*scoreError+valueError := by
  have hprob := weighted_probability_perturbation visible x y v scoreError bound h hs hb hscore hv
  have hval := weighted_magnitude visible y (fun i => v i-u i) valueError (fun i _ => hvalue i) h
  simp_rw [mul_sub, Finset.sum_sub_distrib] at hval
  exact (abs_sub_le _ _ _).trans (add_le_add hprob hval)

theorem weighted_normalization_perturbation {ι : Type} [Fintype ι]
    (w z v : ι → ℝ) (error bound : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : 0 < ∑ i, w i) (ht : 0 < ∑ i, z i) (hb : 0 ≤ bound)
    (he : (∑ i, |w i-z i|) ≤ error) (hv : ∀ i, |v i| ≤ bound) :
    |(∑ i, w i*v i)/(∑ i, w i)-(∑ i, z i*v i)/(∑ i, z i)| ≤
      2*bound*error/(∑ i, z i) := by
  have hnum : |(∑ i, w i*v i)-(∑ i, z i*v i)| ≤ error*bound := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |w i*v i-z i*v i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |w i-z i| * |v i| := by simp only [← sub_mul, abs_mul]
      _ ≤ ∑ i, |w i-z i| * bound :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _))
      _ = (∑ i, |w i-z i|)*bound := (Finset.sum_mul _ _ _).symm
      _ ≤ error*bound := mul_le_mul_of_nonneg_right he hb
  have hmass : |(∑ i, z i)-(∑ i, w i)| ≤ error := by
    rw [abs_sub_comm, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans he
  have hvalue : |(∑ i, w i*v i)/(∑ i, w i)| ≤ bound := by
    rw [abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    calc
      _ ≤ ∑ i, |w i*v i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, w i*|v i| := by simp only [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ i, w i*bound := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (hw i))
      _ = bound*(∑ i, w i) := by rw [← Finset.sum_mul, mul_comm]
  have hid : (∑ i, w i*v i)/(∑ i, w i)-(∑ i, z i*v i)/(∑ i, z i) =
      ((∑ i, w i*v i)-(∑ i, z i*v i))/(∑ i, z i)+
      ((∑ i, w i*v i)/(∑ i, w i))*((∑ i, z i)-(∑ i, w i))/(∑ i, z i) := by
    field_simp
    ring
  rw [hid]
  have hfirst : |((∑ i, w i*v i)-(∑ i, z i*v i))/(∑ i, z i)| ≤ error*bound/(∑ i, z i) := by
    rw [abs_div, abs_of_pos ht]
    exact div_le_div_of_nonneg_right hnum ht.le
  have hsecond : |((∑ i, w i*v i)/(∑ i, w i))*((∑ i, z i)-(∑ i, w i))/(∑ i, z i)| ≤
      bound*error/(∑ i, z i) := by
    rw [abs_div, abs_mul, abs_of_pos ht]
    exact div_le_div_of_nonneg_right (mul_le_mul hvalue hmass (abs_nonneg _) hb) ht.le
  exact ((abs_add_le _ _).trans (add_le_add hfirst hsecond)).trans (by ring_nf; rfl)

theorem weighted_normalization_relative_error {ι : Type} [Fintype ι]
    (w z v : ι → ℝ) (relativeError bound : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : 0 < ∑ i, w i) (ht : 0 < ∑ i, z i) (hb : 0 ≤ bound)
    (he : ∀ i, |w i-z i| ≤ relativeError*z i) (hv : ∀ i, |v i| ≤ bound) :
    |(∑ i, w i*v i)/(∑ i, w i)-(∑ i, z i*v i)/(∑ i, z i)| ≤
      2*bound*relativeError := by
  have hsum : (∑ i, |w i-z i|) ≤ relativeError*(∑ i, z i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => he i)
  have hh := weighted_normalization_perturbation w z v _ bound hw hs ht hb hsum hv
  have hid : 2*bound*(relativeError*(∑ i, z i))/(∑ i, z i) = 2*bound*relativeError := by
    field_simp
  rwa [hid] at hh

#print axioms weighted_probability_perturbation
#print axioms probability_l1_perturbation
#print axioms attention_perturbation
#print axioms weighted_normalization_relative_error
end Project.Softmax.Real
