import Project.SoftmaxWide.Row
import Project.ProofKit.F64DivisionSign
import Project.Softmax.Numerical
import Project.Softmax.RoundedNormalization

namespace Project.SoftmaxWide
open CodeLib.IEEE64 Project.ProofKit Project.Softmax

set_option exponentiation.threshold 4096

theorem probability_roundoff (n i w d : UInt64)
    (hw : Finite w) (hd : Finite d) (bd : 1/2 ≤ value d)
    (bw : 0 ≤ value w ∧ value w ≤ 2) (hz : ¬i < n → w = 0) :
    Finite (probability n i w d) ∧
    |value (probability n i w d)-value w/value d| ≤ 4*arithmeticEpsilon := by
  have dp : 0 < value d := by linarith
  have d0 : Wasm.IEEE64.scaledMagnitude d ≠ 0 := by
    intro hh
    simp [value, Wasm.IEEE64.scaledValue, hh] at dp
  by_cases hi : i < n
  · have hq : |value w/value d| ≤ 4 := by
      rw [abs_of_nonneg (div_nonneg bw.1 dp.le)]
      apply (div_le_iff₀ dp).mpr
      linarith [bw.2]
    have hh := F64ArithmeticBounds.div_error w d hw hd d0 4 (by norm_num) (by norm_num) hq
    simpa only [probability, ite_eq_left hi, mul_comm] using hh
  · have hf0 : Finite 0 := by unfold CodeLib.IEEE64.Finite; decide
    simp [probability, hi, hz hi, hf0, ExpSmall.zero_value, arithmeticEpsilon]

theorem compute_outputs (n a b c d : UInt64) (i : Fin 4) :
    outputs (compute n a b c d) i =
      probability n (indexWord i) (computedWeights n a b c d i) (denominatorWord n a b c d) := by
  fin_cases i <;> rfl

theorem compute_numerical (n a b c d : UInt64) (h : Valid n a b c d) :
    (∀ i, Finite (outputs (compute n a b c d) i)) ∧
    (∑ i, |value (outputs (compute n a b c d) i)-reference n (scores a b c d) i|) ≤
      10053*arithmeticEpsilon ∧
    |(∑ i, value (outputs (compute n a b c d) i))-1| ≤ 52*arithmeticEpsilon := by
  let w := computedWeights n a b c d
  let r := realWeight n (scores a b c d) (rowMaximum n a b c d)
  let den := denominatorWord n a b c d
  let p := fun i => value (outputs (compute n a b c d) i)
  have hw := row_weights n a b c d h
  have hf : ∀ i, Finite (w i) := fun i => (hw.1 i).1
  have hb : ∀ i, 0 ≤ value (w i) ∧ value (w i) ≤ 2 := fun i =>
    ⟨(hw.1 i).2.1, (hw.1 i).2.2.1⟩
  have hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1 := fun i =>
    ⟨(hw.1 i).2.2.2.2.1, (hw.1 i).2.2.2.2.2.1⟩
  have he : ∀ i, |value (w i)-r i| ≤ 5000*arithmeticEpsilon*r i+1/10^27 :=
    fun i => (hw.1 i).2.2.2.2.2.2
  have hd := denominator w r hf hb hr he hw.2
  change Finite den ∧ 1/2 ≤ value den ∧ value den ≤ 5 ∧
    |value den-∑ i, value (w i)| ≤ 18*arithmeticEpsilon ∧
    1/2 ≤ ∑ i, value (w i) ∧ 1 ≤ ∑ i, r i ∧
    (∑ i, |value (w i)-r i|) ≤ 5000*arithmeticEpsilon*(∑ i, r i)+4/10^27 at hd
  have hp (i : Fin 4) := probability_roundoff n (indexWord i) (w i) den
    (hf i) hd.1 hd.2.1 (hb i) (hw.1 i).2.2.2.1
  have hpdiv (i : Fin 4) : |p i-value (w i)/value den| ≤ 4*arithmeticEpsilon := by
    dsimp only [p]
    rw [compute_outputs]
    exact (hp i).2
  have herr : (∑ i, |p i-value (w i)/value den|) ≤ 16*arithmeticEpsilon :=
    (Finset.sum_le_sum (fun i _ => hpdiv i)).trans (by norm_num; ring_nf; rfl)
  have dp : 0 < value den := by linarith [hd.2.1]
  have sp : 0 < ∑ i, value (w i) := by linarith [hd.2.2.2.2.1]
  have rp : 0 < ∑ i, r i := by linarith [hd.2.2.2.2.2.1]
  have heps : 0 ≤ arithmeticEpsilon := by norm_num [arithmeticEpsilon]
  have hsumerror : 18*arithmeticEpsilon/value den ≤ 36*arithmeticEpsilon := by
    apply (div_le_iff₀ dp).mpr
    nlinarith [hd.2.1]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [compute_outputs]
    exact (hp i).1
  · have hl1 := Real.rounded_normalization_l1_error (fun i => value (w i)) r p (value den)
      _ _ _ (fun i => (hb i).1) sp rp dp hd.2.2.2.2.2.2 hd.2.2.2.1 herr
    have hweight : 2*(5000*arithmeticEpsilon*(∑ i, r i)+4/10^27)/(∑ i, r i) ≤
        10000*arithmeticEpsilon+8/10^27 := by
      apply (div_le_iff₀ rp).mpr
      nlinarith [hd.2.2.2.2.2.1]
    have hbound := hl1.trans (add_le_add (add_le_add le_rfl hsumerror) hweight)
    simp only [r, shifted_reference] at hbound
    exact hbound.trans (by norm_num [arithmeticEpsilon])
  · have hdiff : |(∑ i, p i)-(∑ i, value (w i)/value den)| ≤ 16*arithmeticEpsilon := by
      rw [← Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans herr
    have hnorm : |(∑ i, value (w i)/value den)-1| ≤ 36*arithmeticEpsilon := by
      have hid : (∑ i, value (w i)/value den)-1 = ((∑ i, value (w i))-value den)/value den := by
        rw [← Finset.sum_div]
        field_simp
      rw [hid, abs_div, abs_of_pos dp, abs_sub_comm]
      exact (div_le_div_of_nonneg_right hd.2.2.2.1 dp.le).trans hsumerror
    exact (abs_sub_le _ _ _).trans ((add_le_add hdiff hnorm).trans (by ring_nf; rfl))

theorem compute_nonnegative (n a b c d : UInt64) (h : Valid n a b c d) (i : Fin 4) :
    0 ≤ value (outputs (compute n a b c d) i) := by
  let w := computedWeights n a b c d
  let r := realWeight n (scores a b c d) (rowMaximum n a b c d)
  have hw := row_weights n a b c d h
  have hd := denominator w r (fun i => (hw.1 i).1)
    (fun i => ⟨(hw.1 i).2.1, (hw.1 i).2.2.1⟩)
    (fun i => ⟨(hw.1 i).2.2.2.2.1, (hw.1 i).2.2.2.2.2.1⟩)
    (fun i => (hw.1 i).2.2.2.2.2.2) hw.2
  let den := denominatorWord n a b c d
  have hden : 1/2 ≤ value den := hd.2.1
  have dp : 0 < value den := by linarith
  rw [compute_outputs]
  by_cases hi : indexWord i < n
  · simp only [probability, ite_eq_left hi]
    apply F64DivBounds.div_nonnegative _ _ (hw.1 i).1 hd.1 (hw.1 i).2.1 dp
    have hq : |value (w i)/value den| ≤ 4 := by
      rw [abs_of_nonneg (div_nonneg (hw.1 i).2.1 dp.le)]
      apply (div_le_iff₀ dp).mpr
      have hwi : value (w i) ≤ 2 := (hw.1 i).2.2.1
      linarith
    exact hq.trans_lt (by norm_num)
  · simp only [probability, ite_eq_right hi, ExpSmall.zero_value, le_refl]

theorem compute_weighted_error (n a b c d : UInt64) (h : Valid n a b c d)
    (v : Fin 4 → ℝ) (bound : ℝ) (hb : 0 ≤ bound) (hv : ∀ i, |v i| ≤ bound) :
    |(∑ i, value (outputs (compute n a b c d) i)*v i)-
      (∑ i, reference n (scores a b c d) i*v i)| ≤ bound*(10053*arithmeticEpsilon) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |value (outputs (compute n a b c d) i)*v i-reference n (scores a b c d) i*v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |value (outputs (compute n a b c d) i)-reference n (scores a b c d) i| * |v i| := by
      simp only [← sub_mul, abs_mul]
    _ ≤ ∑ i, |value (outputs (compute n a b c d) i)-reference n (scores a b c d) i| * bound :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _))
    _ = (∑ i, |value (outputs (compute n a b c d) i)-reference n (scores a b c d) i|)*bound :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_right (compute_numerical n a b c d h).2.1 hb

#print axioms compute_numerical
#print axioms compute_nonnegative
#print axioms compute_weighted_error
end Project.SoftmaxWide
