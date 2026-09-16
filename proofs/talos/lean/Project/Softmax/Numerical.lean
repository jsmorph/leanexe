import Project.Softmax.Row

namespace Project.Softmax
open CodeLib.IEEE64

def outputs (r : Result) : Fin 4 → UInt64 := ![r.p0, r.p1, r.p2, r.p3]

def computedWeights (n a b c d : UInt64) (i : Fin 4) : UInt64 :=
  weight n (indexWord i) (scores a b c d i) (rowMaximum n a b c d)

def denominatorWord (n a b c d : UInt64) : UInt64 :=
  let w := computedWeights n a b c d
  total (w 0) (w 1) (w 2) (w 3)

theorem compute_outputs (n a b c d : UInt64) (i : Fin 4) :
    outputs (compute n a b c d) i =
      probability n (indexWord i) (computedWeights n a b c d i) (denominatorWord n a b c d) := by
  fin_cases i <;> rfl

def NumericalResult (n a b c d : UInt64) (result : Result) : Prop :=
  result.status = 0 ∧
  (∀ i, Finite (outputs result i) ∧ 0 ≤ value (outputs result i) ∧
    (indexWord i < n → 0 < value (outputs result i)) ∧
    (¬indexWord i < n → outputs result i = 0) ∧
    |value (outputs result i)-reference n (scores a b c d) i| ≤ 1/64) ∧
  |(∑ i, value (outputs result i))-1| ≤ 32*arithmeticEpsilon

theorem compute_numerical (n a b c d : UInt64) (h : Valid n a b c d) :
    NumericalResult n a b c d (compute n a b c d) := by
  let w := computedWeights n a b c d
  let r := realWeight n (scores a b c d) (rowMaximum n a b c d)
  let den := denominatorWord n a b c d
  have hw := row_weights n a b c d h
  have hf : ∀ i, Finite (w i) := fun i => (hw.1 i).1
  have hp : ∀ i, 0 ≤ value (w i) := fun i => (hw.1 i).2.1
  have hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1 := fun i =>
    ⟨(hw.1 i).2.2.2.2.1, (hw.1 i).2.2.2.2.2.1⟩
  have he : ∀ i, |value (w i)-r i| ≤ 1/399 := fun i => (hw.1 i).2.2.2.2.2.2
  have hd := denominator w r hf hp hr he hw.2
  change Finite den ∧ 49/50 ≤ value den ∧ value den ≤ 5 ∧
    |value den-∑ i, r i| ≤ 1/90 ∧
    |value den-∑ i, value (w i)| ≤ 18*arithmeticEpsilon ∧ 1 ≤ ∑ i, r i at hd
  have hb : ∀ i, 0 ≤ value (w i) ∧ value (w i) ≤ 2 := by
    intro i
    exact ⟨hp i, by have hh := (abs_le.mp (he i)).2; linarith [(hr i).2]⟩
  have ho (i : Fin 4) := probability_roundoff n (indexWord i) (w i) den
    (hf i) hd.1 ⟨hd.2.1, hd.2.2.1⟩ (hb i) (hw.1 i).2.2.1 (hw.1 i).2.2.2.1
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    rw [compute_outputs]
    refine ⟨(ho i).1, (ho i).2.1, (ho i).2.2.1, ?_, ?_⟩
    · intro hi
      simp [probability, hi]
    · have hq := quotient_error (value (w i)) (value den) (r i) (∑ j, r j)
        hd.2.1 hd.2.2.2.2.2 (hr i) (he i) hd.2.2.2.1
      rw [shifted_reference] at hq
      exact (abs_sub_le _ _ _).trans ((add_le_add (ho i).2.2.2 hq).trans
        (by norm_num [arithmeticEpsilon]))
  · have herr : |(∑ i, value (outputs (compute n a b c d) i)) -
        (∑ i, value (w i)/value den)| ≤ 12*arithmeticEpsilon := by
      rw [← Finset.sum_sub_distrib]
      have hh : ∀ i, |value (outputs (compute n a b c d) i)-value (w i)/value den| ≤
          3*arithmeticEpsilon := by
        intro i
        rw [compute_outputs]
        exact (ho i).2.2.2
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum (fun i _ => hh i)).trans (by norm_num; ring_nf; rfl))
    have dp : 0 < value den := by linarith [hd.2.1]
    have hid : (∑ i, value (w i)/value den)-1 =
        ((∑ i, value (w i))-value den)/value den := by
      rw [← Finset.sum_div]
      field_simp
    have hnorm : |(∑ i, value (w i)/value den)-1| ≤ 20*arithmeticEpsilon := by
      rw [hid, abs_div, abs_of_pos dp, abs_sub_comm]
      apply (div_le_iff₀ dp).mpr
      have ee : 0 ≤ arithmeticEpsilon := by norm_num [arithmeticEpsilon]
      have hh := mul_le_mul_of_nonneg_left hd.2.1 ee
      nlinarith [hd.2.2.2.2.1]
    exact (abs_sub_le _ _ _).trans ((add_le_add herr hnorm).trans (by ring_nf; rfl))

theorem softmax_success (n a b c d : UInt64) (h : Valid n a b c d) :
    softmax n a b c d = compute n a b c d := by
  simp [softmax, (inDomain_iff n a b c d).mpr h]

theorem softmax_numerical (n a b c d : UInt64) (h : Valid n a b c d) :
    NumericalResult n a b c d (softmax n a b c d) := by
  rw [softmax_success n a b c d h]
  exact compute_numerical n a b c d h

#print axioms compute_numerical
#print axioms softmax_numerical
end Project.Softmax
