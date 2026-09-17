import Project.SoftmaxWide.Weight
import Project.Softmax.Row

namespace Project.SoftmaxWide
open CodeLib.IEEE64 Project.ProofKit Project.Softmax

set_option exponentiation.threshold 4096

def Valid (n a b c d : UInt64) : Prop :=
  0 < n ∧ n ≤ 4 ∧ (∀ i, Finite (scores a b c d i)) ∧
    ∀ i j, indexWord i < n → indexWord j < n →
      |value (scores a b c d i)-value (scores a b c d j)| < (2:ℝ)^1023

def computedWeights (n a b c d : UInt64) (i : Fin 4) : UInt64 :=
  weight n (indexWord i) (scores a b c d i) (rowMaximum n a b c d)

def denominatorWord (n a b c d : UInt64) : UInt64 :=
  let w := computedWeights n a b c d
  total (w 0) (w 1) (w 2) (w 3)

theorem row_weights (n a b c d : UInt64) (h : Valid n a b c d) :
    let w := computedWeights n a b c d
    let r := realWeight n (scores a b c d) (rowMaximum n a b c d)
    (∀ i, Finite (w i) ∧ 0 ≤ value (w i) ∧ value (w i) ≤ 2 ∧
      (¬indexWord i < n → w i = 0) ∧ 0 ≤ r i ∧ r i ≤ 1 ∧
      |value (w i)-r i| ≤ 5000*arithmeticEpsilon*r i+1/10^27) ∧
    ∃ i, r i = 1 := by
  dsimp only
  constructor
  · intro i
    obtain ⟨j, hj, hm⟩ := row_maximum_attained n a b c d h.1
    by_cases hi : indexWord i < n
    · have ho := row_maximum_ge n a b c d i hi
      have hs := shifted_weight _ _ (h.2.2.1 i)
        (by rw [hm]; exact h.2.2.1 j) (by rw [hm]; exact h.2.2.2 i j hi hj) ho
      have hu : Real.exp (value (scores a b c d i)-value (rowMaximum n a b c d)) ≤ 1 := by
        simpa using Real.exp_le_exp.mpr (sub_nonpos.mpr ho)
      simp only [computedWeights, weight, realWeight, ite_eq_left hi]
      exact ⟨hs.1, hs.2.1, hs.2.2.1, fun hh => False.elim (hh hi),
        (Real.exp_pos _).le, hu, hs.2.2.2⟩
    · have hf0 : Finite 0 := by unfold CodeLib.IEEE64.Finite; decide
      simp [computedWeights, weight, realWeight, hi, hf0, ExpSmall.zero_value]
  · obtain ⟨i, hi, hm⟩ := row_maximum_attained n a b c d h.1
    exact ⟨i, by simp [realWeight, hi, hm]⟩

theorem denominator (w : Fin 4 → UInt64) (r : Fin 4 → ℝ)
    (hf : ∀ i, Finite (w i)) (hb : ∀ i, 0 ≤ value (w i) ∧ value (w i) ≤ 2)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (he : ∀ i, |value (w i)-r i| ≤ 5000*arithmeticEpsilon*r i+1/10^27)
    (hone : ∃ i, r i = 1) :
    let d := total (w 0) (w 1) (w 2) (w 3)
    Finite d ∧ 1/2 ≤ value d ∧ value d ≤ 5 ∧
    |value d-∑ i, value (w i)| ≤ 18*arithmeticEpsilon ∧
    1/2 ≤ ∑ i, value (w i) ∧ 1 ≤ ∑ i, r i ∧
    (∑ i, |value (w i)-r i|) ≤ 5000*arithmeticEpsilon*(∑ i, r i)+4/10^27 := by
  have ht := total_roundoff w hf hb
  have hsum : (∑ i, |value (w i)-r i|) ≤ 5000*arithmeticEpsilon*(∑ i, r i)+4/10^27 := by
    calc
      _ ≤ ∑ i, (5000*arithmeticEpsilon*r i+1/10^27) := Finset.sum_le_sum (fun i _ => he i)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; norm_num
  have hlo : 1 ≤ ∑ i, r i := by
    obtain ⟨i, hi⟩ := hone
    rw [← hi]
    exact Finset.single_le_sum (fun j _ => (hr j).1) (Finset.mem_univ i)
  have hhi : (∑ i, r i) ≤ 4 :=
    (Finset.sum_le_sum (fun i _ => (hr i).2)).trans (by norm_num)
  have hmass : |(∑ i, value (w i))-(∑ i, r i)| ≤ 5000*arithmeticEpsilon*(∑ i, r i)+4/10^27 := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hsum
  have hmass1 := (abs_le.mp hmass).1
  have hmass2 := (abs_le.mp hmass).2
  have ht1 := (abs_le.mp ht.2).1
  have ht2 := (abs_le.mp ht.2).2
  refine ⟨ht.1, ?_, ?_, ht.2, ?_, hlo, hsum⟩ <;>
    norm_num [arithmeticEpsilon] at hmass1 hmass2 ht1 ht2 ⊢ <;> linarith

#print axioms row_weights
#print axioms denominator
end Project.SoftmaxWide
