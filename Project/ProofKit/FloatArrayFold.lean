import Project.ProofKit.F64Bits

/-!
`FloatArray.foldl` in terms of `Array.foldl` on the floats it holds.  Lean core
defines the fold's loop as a private declaration, so the proof opens it.
-/

namespace Project.ProofKit.FloatArrayFold

open private FloatArray.foldlM.loop from Init.Data.FloatArray.Basic

theorem loop_toList {m : Type v → Type w} [Monad m] {f : β → Float → m β} {xs : FloatArray}
    {i j : Nat} (H : xs.size ≤ i + j) {b : β} :
    FloatArray.foldlM.loop f xs xs.size (Nat.le_refl _) i j b =
      (xs.data.toList.drop j).foldlM f b := by
  unfold FloatArray.foldlM.loop
  split; split
  · cases Nat.not_le_of_gt ‹_› (Nat.zero_add _ ▸ H)
  · rename_i i; rw [Nat.succ_add] at H
    simp only [loop_toList (j := j + 1) H]
    rw (occs := [2]) [← List.getElem_cons_drop (as := xs.data.toList) ‹_›]
    simp only [List.foldlM_cons, Array.getElem_toList]
    rfl
  · rw [List.drop_of_length_le (Nat.ge_of_not_lt ‹_›)]; simp

/-- `FloatArray.foldl` folds over the array of floats it holds. -/
theorem foldl_data (f : β → Float → β) (init : β) (xs : FloatArray) :
    xs.foldl f init = xs.data.foldl f init := by
  rw [← Array.foldl_toList, List.foldl_eq_foldlM]
  simp only [FloatArray.foldl, FloatArray.foldlM, Nat.le_refl, dite_true, Nat.sub_zero]
  rw [loop_toList (by omega)]
  rfl

/-- A fold over a `FloatArray` corresponds to a fold over the bit patterns of its
elements when `g` computes the image under `h` of each step of `f`. -/
theorem foldl_toBits {f : β → Float → β} {g : γ → UInt64 → γ} (h : β → γ)
    (hg : ∀ a x, g (h a) x.toBits = h (f a x)) (xs : FloatArray) (init : β) :
    (xs.data.map Float.toBits).foldl g (h init) = h (xs.foldl f init) := by
  rw [foldl_data, Array.foldl_map]
  exact Array.foldl_hom h hg

end Project.ProofKit.FloatArrayFold
