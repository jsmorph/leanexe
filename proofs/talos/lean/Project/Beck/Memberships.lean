import Project.Beck.State

namespace Project.Beck.Memberships

open LeanExe.Examples.Beck

def selected (categories : Nat) (row : Array UInt64) : Finset (Fin categories) :=
  Finset.univ.filter fun category => row[category.val]! = 1

structure Valid (categories : Nat) (row : Array UInt64) : Prop where
  size : row.size = categories
  binary : ∀ category < categories, row[category]! = 0 ∨ row[category]! = 1

theorem initial (categories : Nat) : Valid categories (Array.replicate categories 0) := by
  constructor
  · simp
  · intro category bounded
    left
    simp [getElem!_pos (Array.replicate categories (0 : UInt64)) category (by simpa)]

theorem initial_selected (categories : Nat) :
    selected categories (Array.replicate categories 0) = ∅ := by
  ext category
  simp [selected]

theorem set_valid (categories : Nat) (row : Array UInt64) (valid : Valid categories row)
    (category : Fin categories) : Valid categories (row.set! category.val 1) := by
  constructor
  · simpa using valid.size
  · intro j hj
    by_cases equal : category.val = j
    · subst j
      right
      exact Array.getElem!_set!_self _ _ _ (by rw [valid.size]; exact category.isLt)
    · rw [Array.getElem!_set!_ne _ _ _ _ equal]
      exact valid.binary j hj

theorem selected_set (categories : Nat) (row : Array UInt64) (valid : Valid categories row)
    (category : Fin categories) :
    selected categories (row.set! category.val 1) = insert category (selected categories row) := by
  ext j
  simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases equal : category = j
  · subst j
    rw [Array.getElem!_set!_self _ _ _ (by rw [valid.size]; exact category.isLt)]
    simp
  · have different : category.val ≠ j.val := fun h => equal (Fin.ext h)
    rw [Array.getElem!_set!_ne _ _ _ _ different]
    simp [Ne.symm equal]

theorem read_spec (count : Nat) (words : Array UInt64) (pos categories : Nat)
    (row out : Array UInt64) (valid : Valid categories row)
    (accepted : readMemberships count words pos categories row = some out) :
    Valid categories out ∧ (selected categories out).card = (selected categories row).card + count ∧
      ∀ category : Fin categories, category ∈ selected categories out ↔
        category ∈ selected categories row ∨
          ∃ k < count, words[pos + k]!.toNat = category.val := by
  induction count generalizing pos row with
  | zero =>
    simp only [readMemberships, Option.some.injEq] at accepted
    subst out
    exact ⟨valid, by simp, by simp⟩
  | succ count ih =>
    simp only [readMemberships] at accepted
    split at accepted
    · contradiction
    rename_i bounded
    split at accepted
    · contradiction
    rename_i fresh
    have fresh' : row[words[pos]!.toNat]! = 0 := by simpa using fresh
    let category : Fin categories := ⟨words[pos]!.toNat, by omega⟩
    have nextValid := set_valid categories row valid category
    have result := ih (pos + 1) (row.set! category.val 1) nextValid accepted
    have notSelected : category ∉ selected categories row := by
      simp [selected, category, fresh']
    refine ⟨result.1, ?_, ?_⟩
    · rw [result.2.1, selected_set categories row valid category,
        Finset.card_insert_of_notMem notSelected]
      omega
    · intro j
      rw [result.2.2, selected_set categories row valid category]
      simp only [Finset.mem_insert]
      constructor
      · rintro ((equal | old) | ⟨k, hk, value⟩)
        · right
          exact ⟨0, by omega, by simpa [category] using congrArg Fin.val equal.symm⟩
        · exact Or.inl old
        · right
          exact ⟨k + 1, by omega, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using value⟩
      · rintro (old | ⟨k, hk, value⟩)
        · exact Or.inl (Or.inr old)
        · cases k with
          | zero => exact Or.inl (Or.inl (Fin.ext (by simpa [category] using value.symm)))
          | succ k => exact Or.inr ⟨k, by omega,
              by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using value⟩

end Project.Beck.Memberships
