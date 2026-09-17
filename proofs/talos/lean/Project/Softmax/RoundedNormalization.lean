import Project.Softmax.WeightedPerturbation
import Mathlib.Algebra.BigOperators.Field

namespace Project.Softmax.Real

theorem normalization_l1_error {ι : Type} [Fintype ι]
    (w z : ι → ℝ) (error : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : 0 < ∑ i, w i) (ht : 0 < ∑ i, z i)
    (he : (∑ i, |w i-z i|) ≤ error) :
    (∑ i, |w i/(∑ j, w j)-z i/(∑ j, z j)|) ≤ 2*error/(∑ i, z i) := by
  let v := fun i => if 0 ≤ w i/(∑ j, w j)-z i/(∑ j, z j) then (1:ℝ) else -1
  have hv (i : ι) : |v i| ≤ 1 := by dsimp [v]; split <;> norm_num
  have hh := weighted_normalization_perturbation w z v error 1 hw hs ht (by norm_num) he hv
  have hid : (∑ i, w i*v i)/(∑ i, w i)-(∑ i, z i*v i)/(∑ i, z i) =
      ∑ i, |w i/(∑ j, w j)-z i/(∑ j, z j)| := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [v]
    split_ifs with hi
    · rw [abs_of_nonneg hi]
      ring
    · rw [abs_of_neg (lt_of_not_ge hi)]
      ring
  rw [hid, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))] at hh
  simpa only [mul_one] using hh

theorem common_denominator_l1_error {ι : Type} [Fintype ι]
    (w : ι → ℝ) (d : ℝ) (hw : ∀ i, 0 ≤ w i) (hs : 0 < ∑ i, w i) (hd : 0 < d) :
    (∑ i, |w i/d-w i/(∑ j, w j)|) = |d-(∑ i, w i)|/d := by
  have hid (i : ι) : w i/d-w i/(∑ j, w j) = w i*((∑ j, w j)-d)/(d*(∑ j, w j)) := by
    field_simp
  simp_rw [hid, abs_div, abs_mul, abs_of_nonneg (hw _), abs_of_pos hd, abs_of_pos hs]
  rw [← Finset.sum_div, ← Finset.sum_mul, abs_sub_comm]
  field_simp

theorem rounded_normalization_l1_error {ι : Type} [Fintype ι]
    (w z p : ι → ℝ) (d weightError sumError divError : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : 0 < ∑ i, w i) (ht : 0 < ∑ i, z i) (hd : 0 < d)
    (he : (∑ i, |w i-z i|) ≤ weightError)
    (hsum : |d-(∑ i, w i)| ≤ sumError)
    (hdiv : (∑ i, |p i-w i/d|) ≤ divError) :
    (∑ i, |p i-z i/(∑ j, z j)|) ≤ divError+sumError/d+2*weightError/(∑ i, z i) := by
  have hn := normalization_l1_error w z weightError hw hs ht he
  have hden : (∑ i, |w i/d-w i/(∑ j, w j)|) ≤ sumError/d := by
    rw [common_denominator_l1_error w d hw hs hd]
    exact div_le_div_of_nonneg_right hsum hd.le
  calc
    _ ≤ ∑ i, (|p i-w i/d|+|w i/d-w i/(∑ j, w j)|+|w i/(∑ j, w j)-z i/(∑ j, z j)|) := by
      apply Finset.sum_le_sum
      intro i _
      exact (abs_sub_le _ _ _).trans (add_le_add (abs_sub_le _ _ _) le_rfl)
    _ = (∑ i, |p i-w i/d|)+(∑ i, |w i/d-w i/(∑ j, w j)|)+
        (∑ i, |w i/(∑ j, w j)-z i/(∑ j, z j)|) := by simp only [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (add_le_add hdiv hden) hn

#print axioms rounded_normalization_l1_error
end Project.Softmax.Real
