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

end Verified
