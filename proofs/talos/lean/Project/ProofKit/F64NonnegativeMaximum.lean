import Project.ProofKit.F64Maximum

namespace Project.ProofKit.F64Order
open CodeLib.IEEE64

def NonnegativeWord (word : UInt64) : Prop :=
  word = 0 ∨ positiveBits word = true

theorem zero_value : value (0 : UInt64) = 0 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]

theorem nonnegativeWord_spec {word : UInt64} (h : NonnegativeWord word) :
    CodeLib.IEEE64.Finite word ∧ 0 ≤ value word := by
  rcases h with rfl | h
  · exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by rw [zero_value]⟩
  · exact ⟨(positiveBits_spec word h).1, (positiveBits_spec word h).2.le⟩

theorem word_zero_max (word : UInt64) : max 0 word = word := by
  have h : (0 : UInt64) ≤ word := by
    apply UInt64.le_iff_toNat_le.mpr
    simp
  change (if (0 : UInt64) ≤ word then word else 0) = word
  rw [ite_eq_left h]

theorem word_max_zero (word : UInt64) : max word 0 = word := by
  change (if word ≤ (0 : UInt64) then 0 else word) = word
  split
  · rename_i h
    apply UInt64.toNat.inj
    change 0 = word.toNat
    have ht : word.toNat ≤ 0 := UInt64.le_iff_toNat_le.mp h
    omega
  · rfl

theorem nonnegative_max_value {left right : UInt64}
    (hl : NonnegativeWord left) (hr : NonnegativeWord right) :
    NonnegativeWord (max left right) ∧
      value (max left right) = max (value left) (value right) := by
  rcases hl with rfl | hl
  · rw [word_zero_max, zero_value, max_eq_right (nonnegativeWord_spec hr).2]
    exact ⟨hr, rfl⟩
  rcases hr with rfl | hr
  · rw [word_max_zero, zero_value, max_eq_left (positiveBits_spec left hl).2.le]
    exact ⟨Or.inr hl, rfl⟩
  have h := positive_max_value left right hl hr
  exact ⟨Or.inr h.1, h.2⟩

theorem nonnegative_fold_max {words : List UInt64} {initial : UInt64}
    (hw : ∀ word ∈ words, NonnegativeWord word) (hi : NonnegativeWord initial) :
    NonnegativeWord (words.foldl max initial) ∧
      value initial ≤ value (words.foldl max initial) ∧
      ∀ word ∈ words, value word ≤ value (words.foldl max initial) := by
  induction words generalizing initial with
  | nil => exact ⟨hi, le_rfl, by simp⟩
  | cons word words ih =>
      have hm := nonnegative_max_value hi (hw word (by simp))
      have ht := ih (fun item h => hw item (by simp [h])) hm.1
      refine ⟨ht.1, ?_, ?_⟩
      · have hlo : value initial ≤ value (max initial word) := by
          rw [hm.2]
          exact le_max_left _ _
        exact hlo.trans ht.2.1
      · intro item h
        rcases List.mem_cons.mp h with heq | h
        · subst item
          have hlo : value word ≤ value (max initial word) := by
            rw [hm.2]
            exact le_max_right _ _
          exact hlo.trans ht.2.1
        · exact ht.2.2 item h

#print axioms nonnegative_max_value
#print axioms nonnegative_fold_max

end Project.ProofKit.F64Order
