import Project.Softmax.Normalization

namespace Project.Softmax
open CodeLib.IEEE64

def scores (a b c d : UInt64) : Fin 4 → UInt64 := ![a, b, c, d]
def indexWord (i : Fin 4) : UInt64 := UInt64.ofNat i.val

def Valid (n a b c d : UInt64) : Prop :=
  0 < n ∧ n ≤ 4 ∧ ∀ i, Finite (scores a b c d i) ∧ |value (scores a b c d i)| ≤ 4

def SpreadValid (n a b c d : UInt64) : Prop :=
  0 < n ∧ n ≤ 4 ∧ (∀ i, Finite (scores a b c d i)) ∧
    ∀ i j, indexWord i < n → indexWord j < n →
      |value (scores a b c d i)-value (scores a b c d j)| ≤ 16

theorem valid_spread (n a b c d : UInt64) (h : Valid n a b c d) : SpreadValid n a b c d := by
  refine ⟨h.1, h.2.1, fun i => (h.2.2 i).1, ?_⟩
  intro i j _ _
  exact (abs_sub _ _).trans (by linarith [(h.2.2 i).2, (h.2.2 j).2])

theorem inDomain_iff (n a b c d : UInt64) : inDomain n a b c d = true ↔ Valid n a b c d := by
  simp only [inDomain, Bool.and_eq_true, decide_eq_true_eq, bounded_iff, Valid]
  constructor
  · rintro ⟨⟨⟨⟨⟨hn, hn4⟩, ha⟩, hb⟩, hc⟩, hd⟩
    refine ⟨hn, hn4, ?_⟩
    intro i
    fin_cases i <;> simp [scores, ha, hb, hc, hd]
  · rintro ⟨hn, hn4, h⟩
    exact ⟨⟨⟨⟨⟨hn, hn4⟩, h 0⟩, h 1⟩, h 2⟩, h 3⟩

theorem row_maximum_bounds (n a b c d : UInt64) (h : Valid n a b c d) :
    Finite (rowMaximum n a b c d) ∧ |value (rowMaximum n a b c d)| ≤ 4 := by
  have combine (x y : UInt64) (hx : Finite x ∧ |value x| ≤ 4)
      (hy : Finite y ∧ |value y| ≤ 4) : Finite (maximum x y) ∧ |value (maximum x y)| ≤ 4 := by
    rcases maximum_choice x y with hh | hh <;> rw [hh] <;> assumption
  have active (i : UInt64) (x : UInt64) (hx : Finite x ∧ |value x| ≤ 4) :
      Finite (activeScore n i x a) ∧ |value (activeScore n i x a)| ≤ 4 := by
    unfold activeScore
    split
    · exact hx
    · exact h.2.2 0
  exact combine _ _ (combine _ _ (h.2.2 0) (active 1 b (h.2.2 1)))
    (combine _ _ (active 2 c (h.2.2 2)) (active 3 d (h.2.2 3)))

theorem row_maximum_ge (n a b c d : UInt64) (i : Fin 4) (hi : indexWord i < n) :
    value (scores a b c d i) ≤ value (rowMaximum n a b c d) := by
  simp only [rowMaximum, maximum_value]
  fin_cases i
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · change (1 : UInt64) < n at hi
    simp only [activeScore, if_pos hi]
    exact (le_max_right _ _).trans (le_max_left _ _)
  · change (2 : UInt64) < n at hi
    simp only [activeScore, if_pos hi]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · change (3 : UInt64) < n at hi
    simp only [activeScore, if_pos hi]
    exact (le_max_right _ _).trans (le_max_right _ _)

theorem row_maximum_attained (n a b c d : UInt64) (hn : 0 < n) :
    ∃ i, indexWord i < n ∧ rowMaximum n a b c d = scores a b c d i := by
  have first : ∃ i, indexWord i < n ∧ a = scores a b c d i := ⟨0, hn, rfl⟩
  have active (i : Fin 4) :
      ∃ j, indexWord j < n ∧ activeScore n (indexWord i) (scores a b c d i) a = scores a b c d j := by
    unfold activeScore
    split
    · rename_i hi
      exact ⟨i, hi, rfl⟩
    · exact first
  have combine (x y : UInt64)
      (hx : ∃ i, indexWord i < n ∧ x = scores a b c d i)
      (hy : ∃ i, indexWord i < n ∧ y = scores a b c d i) :
      ∃ i, indexWord i < n ∧ maximum x y = scores a b c d i := by
    rcases maximum_choice x y with hh | hh <;> rw [hh] <;> assumption
  exact combine _ _ (combine _ _ first (active 1)) (combine _ _ (active 2) (active 3))

noncomputable def realWeight (n : UInt64) (s : Fin 4 → UInt64) (m : UInt64) (i : Fin 4) : ℝ :=
  if indexWord i < n then Real.exp (value (s i)-value m) else 0

noncomputable def unshifted (n : UInt64) (s : Fin 4 → UInt64) (i : Fin 4) : ℝ :=
  if indexWord i < n then Real.exp (value (s i)) else 0

noncomputable def reference (n : UInt64) (s : Fin 4 → UInt64) (i : Fin 4) : ℝ :=
  unshifted n s i / ∑ j, unshifted n s j

theorem shifted_reference (n : UInt64) (s : Fin 4 → UInt64) (m : UInt64) (i : Fin 4) :
    realWeight n s m i / ∑ j, realWeight n s m j = reference n s i := by
  have hi (j : Fin 4) : realWeight n s m j = unshifted n s j / Real.exp (value m) := by
    unfold realWeight unshifted
    split <;> simp [Real.exp_sub]
  simp only [hi, ← Finset.sum_div, reference]
  exact div_div_div_cancel_right₀ (ne_of_gt (Real.exp_pos _)) _ _

theorem row_weights_spread (n a b c d : UInt64) (h : SpreadValid n a b c d) :
    let s := scores a b c d
    let m := rowMaximum n a b c d
    (∀ i, Finite (weight n (indexWord i) (s i) m) ∧
      0 ≤ value (weight n (indexWord i) (s i) m) ∧
      (indexWord i < n → 1/1000000000 ≤ value (weight n (indexWord i) (s i) m)) ∧
      (¬indexWord i < n → weight n (indexWord i) (s i) m = 0) ∧
      0 ≤ realWeight n s m i ∧ realWeight n s m i ≤ 1 ∧
      |value (weight n (indexWord i) (s i) m)-realWeight n s m i| ≤ 1/299000) ∧
    ∃ i, realWeight n s m i = 1 := by
  dsimp only
  constructor
  · intro i
    obtain ⟨j, hj, hm⟩ := row_maximum_attained n a b c d h.1
    by_cases hi : indexWord i < n
    · have ho := row_maximum_ge n a b c d i hi
      have hs := shifted_weight_sixteen _ _ (h.2.2.1 i)
        (by rw [hm]; exact h.2.2.1 j) (by rw [hm]; exact h.2.2.2 i j hi hj) ho
      have hu : Real.exp (value (scores a b c d i)-value (rowMaximum n a b c d)) ≤ 1 := by
        simpa using Real.exp_le_exp.mpr (sub_nonpos.mpr ho)
      simp only [weight, realWeight, if_pos hi]
      exact ⟨hs.1, by linarith [hs.2.1], fun _ => hs.2.1, fun hh => False.elim (hh hi),
        (Real.exp_pos _).le, hu, hs.2.2⟩
    · have hf0 : Finite 0 := by unfold CodeLib.IEEE64.Finite; decide
      have hv0 : value 0 = 0 := by
        norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
          Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
      simp [weight, realWeight, hi, hf0, hv0]
  · obtain ⟨i, hi, hm⟩ := row_maximum_attained n a b c d h.1
    exact ⟨i, by simp [realWeight, hi, hm]⟩

theorem row_weights (n a b c d : UInt64) (h : Valid n a b c d) :
    let s := scores a b c d
    let m := rowMaximum n a b c d
    (∀ i, Finite (weight n (indexWord i) (s i) m) ∧
      0 ≤ value (weight n (indexWord i) (s i) m) ∧
      (indexWord i < n → 1/1000000000 ≤ value (weight n (indexWord i) (s i) m)) ∧
      (¬indexWord i < n → weight n (indexWord i) (s i) m = 0) ∧
      0 ≤ realWeight n s m i ∧ realWeight n s m i ≤ 1 ∧
      |value (weight n (indexWord i) (s i) m)-realWeight n s m i| ≤ 1/299000) ∧
    ∃ i, realWeight n s m i = 1 :=
  row_weights_spread n a b c d (valid_spread n a b c d h)

#print axioms inDomain_iff
#print axioms shifted_reference
#print axioms row_weights
end Project.Softmax
