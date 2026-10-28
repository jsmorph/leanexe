import Verified.TreeFieldLocs

namespace Verified

theorem treeFieldLocs_word_get (fields : List Bool) :
    ∀ wordBase childBase (i : Fin (fields.count false)),
      (treeFieldLocs fields wordBase childBase)[(fieldPosition false fields i).val]'(by
        rw [treeFieldLocs_length]; exact (fieldPosition false fields i).isLt) = wordBase + i.val := by
  induction fields with
  | nil => intro wordBase childBase i; exact Fin.elim0 i
  | cons bit rest ih =>
    intro wordBase childBase i
    cases bit
    · by_cases hz : i.val = 0
      · simp [fieldPosition, hz, treeFieldLocs]
      · rw [fieldPosition, dite_eq_left rfl, dite_eq_right hz]
        simp only [Fin.val_succ, treeFieldLocs, List.getElem_cons_succ]
        rw [ih]
        simp only
        omega
    · simp only [fieldPosition, dite_eq_right (by decide : true ≠ false), Fin.val_succ,
        treeFieldLocs, List.getElem_cons_succ]
      exact ih _ _ _

theorem treeFieldLocs_child_get (fields : List Bool) :
    ∀ wordBase childBase (i : Fin (fields.count true)),
      (treeFieldLocs fields wordBase childBase)[(fieldPosition true fields i).val]'(by
        rw [treeFieldLocs_length]; exact (fieldPosition true fields i).isLt) = childBase + i.val := by
  induction fields with
  | nil => intro wordBase childBase i; exact Fin.elim0 i
  | cons bit rest ih =>
    intro wordBase childBase i
    cases bit
    · simp only [fieldPosition, dite_eq_right (by decide : false ≠ true), Fin.val_succ,
        treeFieldLocs, List.getElem_cons_succ]
      exact ih _ _ _
    · by_cases hz : i.val = 0
      · simp [fieldPosition, hz, treeFieldLocs]
      · rw [fieldPosition, dite_eq_left rfl, dite_eq_right hz]
        simp only [Fin.val_succ, treeFieldLocs, List.getElem_cons_succ]
        rw [ih]
        simp only
        omega

/-- The type of the slot of word `i` is the type of word `i`. -/
theorem treeFieldTypes_word_get (fields : List Bool) :
    ∀ (tys : List Wasm.ValueType) (i : Fin (fields.count false)),
      (treeFieldTypes fields tys).getD (fieldPosition false fields i).val .i64 =
        tys.getD i.val .i64 := by
  induction fields with
  | nil => intro tys i; exact Fin.elim0 i
  | cons bit rest ih =>
    intro tys i
    cases bit
    · by_cases hz : i.val = 0
      · simp only [fieldPosition, dite_true, hz, treeFieldTypes, List.getD_cons_zero]
        cases tys <;> rfl
      · rw [fieldPosition, dite_eq_left rfl, dite_eq_right hz]
        simp only [Fin.val_succ, treeFieldTypes, List.getD_cons_succ]
        rw [ih]
        obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
        simp only [hk, Nat.add_sub_cancel]
        cases tys <;> simp
    · simp only [fieldPosition, dite_eq_right (by decide : true ≠ false), Fin.val_succ,
        treeFieldTypes, List.getD_cons_succ]
      exact ih _ _

/-- The slot of a child has type i64. -/
theorem treeFieldTypes_child_get (fields : List Bool) :
    ∀ (tys : List Wasm.ValueType) (i : Fin (fields.count true)),
      (treeFieldTypes fields tys).getD (fieldPosition true fields i).val .i64 = .i64 := by
  induction fields with
  | nil => intro tys i; exact Fin.elim0 i
  | cons bit rest ih =>
    intro tys i
    cases bit
    · simp only [fieldPosition, dite_eq_right (by decide : false ≠ true), Fin.val_succ,
        treeFieldTypes, List.getD_cons_succ]
      exact ih _ _
    · by_cases hz : i.val = 0
      · simp [fieldPosition, hz, treeFieldTypes]
      · rw [fieldPosition, dite_eq_left rfl, dite_eq_right hz]
        simp only [Fin.val_succ, treeFieldTypes, List.getD_cons_succ]
        exact ih _ _

theorem treeFieldTypes_length (fields : List Bool) :
    ∀ tys, (treeFieldTypes fields tys).length = fields.length := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih => cases bit <;> intro tys <;> simp only [treeFieldTypes, List.length_cons, ih]

end Verified
