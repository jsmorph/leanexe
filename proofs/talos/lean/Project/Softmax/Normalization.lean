import Project.Softmax.Weight

namespace Project.Softmax
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem sum_four (f : Fin 4 → ℝ) : (∑ i, f i) = f 0+f 1+f 2+f 3 := by
  simp [Fin.sum_univ_succ]
  ring

theorem total_roundoff (w : Fin 4 → UInt64)
    (hf : ∀ i, Finite (w i)) (hb : ∀ i, 0 ≤ value (w i) ∧ value (w i) ≤ 2) :
    Finite (total (w 0) (w 1) (w 2) (w 3)) ∧
    |value (total (w 0) (w 1) (w 2) (w 3)) - ∑ i, value (w i)| ≤ 18*arithmeticEpsilon := by
  have pair (i j : Fin 4) := F64ArithmeticBounds.add_error (w i) (w j) (hf i) (hf j)
    4 (by norm_num) (by norm_num)
    (by rw [abs_of_nonneg (add_nonneg (hb i).1 (hb j).1)]; linarith [(hb i).2, (hb j).2])
  have h01 := pair 0 1
  have h23 := pair 2 3
  have b01 : |value (Wasm.IEEE64.add (w 0) (w 1))| ≤ 5 := by
    have h := F64ArithmeticBounds.magnitude_of_error _ _ _ 4 h01.2
      (by rw [abs_of_nonneg (add_nonneg (hb 0).1 (hb 1).1)]; linarith [(hb 0).2, (hb 1).2])
    exact h.trans (by norm_num [arithmeticEpsilon])
  have b23 : |value (Wasm.IEEE64.add (w 2) (w 3))| ≤ 5 := by
    have h := F64ArithmeticBounds.magnitude_of_error _ _ _ 4 h23.2
      (by rw [abs_of_nonneg (add_nonneg (hb 2).1 (hb 3).1)]; linarith [(hb 2).2, (hb 3).2])
    exact h.trans (by norm_num [arithmeticEpsilon])
  have hs := F64ArithmeticBounds.add_error _ _ h01.1 h23.1 10 (by norm_num) (by norm_num)
    ((abs_add_le _ _).trans (by linarith))
  refine ⟨hs.1, ?_⟩
  rw [sum_four]
  have h1 := abs_le.mp h01.2
  have h2 := abs_le.mp h23.2
  have h3 := abs_le.mp hs.2
  apply abs_le.mpr
  dsimp only [total]
  constructor <;> linarith

theorem denominator (w : Fin 4 → UInt64) (r : Fin 4 → ℝ)
    (hf : ∀ i, Finite (w i)) (hp : ∀ i, 0 ≤ value (w i))
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (he : ∀ i, |value (w i)-r i| ≤ 1/299000) (hone : ∃ i, r i = 1) :
    let d := total (w 0) (w 1) (w 2) (w 3)
    Finite d ∧ 49/50 ≤ value d ∧ value d ≤ 5 ∧
    |value d - ∑ i, r i| ≤ 1/74000 ∧
    |value d - ∑ i, value (w i)| ≤ 18*arithmeticEpsilon ∧
    1 ≤ ∑ i, r i := by
  have hb : ∀ i, 0 ≤ value (w i) ∧ value (w i) ≤ 2 := by
    intro i
    exact ⟨hp i, by have h := (abs_le.mp (he i)).2; linarith [(hr i).2]⟩
  have ht := total_roundoff w hf hb
  have hsum : |(∑ i, value (w i)) - ∑ i, r i| ≤ 4/299000 := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun i _ => he i)).trans (by norm_num))
  have herror : |value (total (w 0) (w 1) (w 2) (w 3)) - ∑ i, r i| ≤ 1/74000 :=
    (abs_sub_le _ _ _).trans ((add_le_add ht.2 hsum).trans (by norm_num [arithmeticEpsilon]))
  have hlo : 1 ≤ ∑ i, r i := by
    obtain ⟨i, hi⟩ := hone
    rw [← hi]
    exact Finset.single_le_sum (fun j _ => (hr j).1) (Finset.mem_univ i)
  have hhi : (∑ i, r i) ≤ 4 :=
    (Finset.sum_le_sum (fun i _ => (hr i).2)).trans (by norm_num)
  have ha := abs_le.mp herror
  exact ⟨ht.1, by linarith, by linarith, herror, ht.2, hlo⟩

theorem quotient_error (w d r s : ℝ) (hd : 49/50 ≤ d) (hs : 1 ≤ s)
    (hr : 0 ≤ r ∧ r ≤ 1) (hw : |w-r| ≤ 1/299000) (he : |d-s| ≤ 1/74000) :
    |w/d-r/s| ≤ 1/58000 := by
  have dp : 0 < d := by linarith
  have sp : 0 < s := by linarith
  have hid : w/d-r/s = ((w-r)*s+r*(s-d))/(d*s) := by field_simp; ring
  rw [hid, abs_div, abs_of_pos (mul_pos dp sp)]
  apply (div_le_iff₀ (mul_pos dp sp)).mpr
  have h1 : |(w-r)*s| ≤ (1/299000)*s := by
    rw [abs_mul, abs_of_pos sp]
    exact mul_le_mul_of_nonneg_right hw sp.le
  have h2 : |r*(s-d)| ≤ 1/74000 := by
    rw [abs_mul, abs_of_nonneg hr.1, abs_sub_comm]
    have hh := mul_le_mul_of_nonneg_left he hr.1
    nlinarith [hr.2]
  have ht := abs_add_le ((w-r)*s) (r*(s-d))
  have hds := mul_le_mul_of_nonneg_right hd sp.le
  nlinarith

theorem probability_roundoff (n i w d : UInt64)
    (hw : Finite w) (hd : Finite d) (bd : 49/50 ≤ value d ∧ value d ≤ 5)
    (bw : 0 ≤ value w ∧ value w ≤ 2)
    (hl : i < n → 1/1000000000 ≤ value w) (hz : ¬i < n → w = 0) :
    Finite (probability n i w d) ∧ 0 ≤ value (probability n i w d) ∧
    (i < n → 0 < value (probability n i w d)) ∧
    |value (probability n i w d) - value w/value d| ≤ 3*arithmeticEpsilon := by
  have dp : 0 < value d := by linarith [bd.1]
  have d0 : Wasm.IEEE64.scaledMagnitude d ≠ 0 := by
    intro hh
    simp [value, Wasm.IEEE64.scaledValue, hh] at dp
  by_cases h : i < n
  · have bq : |value w/value d| ≤ 3 := by
      rw [abs_of_nonneg (div_nonneg bw.1 dp.le)]
      apply (div_le_iff₀ dp).mpr
      linarith [bd.1, bw.2]
    have hs := F64ArithmeticBounds.div_error w d hw hd d0 3 (by norm_num) (by norm_num) bq
    have ql : (1/5000000000:ℝ) ≤ value w/value d := by
      apply (le_div_iff₀ dp).mpr
      linarith [hl h, bd.2]
    have he := (abs_le.mp hs.2).1
    have hp : 0 < value (Wasm.IEEE64.div w d) := by
      have ee : 3*arithmeticEpsilon < (1/5000000000:ℝ) := by norm_num [arithmeticEpsilon]
      linarith
    simp only [probability, if_pos h]
    exact ⟨hs.1, hp.le, fun _ => hp, by simpa [mul_comm] using hs.2⟩
  · have hf0 : Finite 0 := by unfold CodeLib.IEEE64.Finite; decide
    have hv0 : value 0 = 0 := by
      norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
        Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
    simp [probability, h, hz h, hf0, hv0, arithmeticEpsilon]

#print axioms denominator
#print axioms quotient_error
#print axioms probability_roundoff
end Project.Softmax
