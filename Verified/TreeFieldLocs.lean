import Verified.TreeFieldsCode
import Verified.TreeLayout

namespace Verified

theorem treeFieldLocs_length (fields : List Bool) :
    ∀ words children, (treeFieldLocs fields words children).length = fields.length := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih => cases bit <;> intros <;> simp only [treeFieldLocs, List.length_cons, ih]

theorem treeFieldLocs_mem (fields : List Bool) :
    ∀ words children loc,
      loc ∈ treeFieldLocs fields words children ↔
        (words ≤ loc ∧ loc < words + fields.count false) ∨
          (children ≤ loc ∧ loc < children + fields.count true) := by
  induction fields with
  | nil => intros; simp [treeFieldLocs]
  | cons bit rest ih =>
    cases bit <;> intro words children loc <;>
      simp only [treeFieldLocs, List.mem_cons, ih] <;>
      simp [List.count_cons] <;> omega

theorem treeFieldLocs_nodup (fields : List Bool) :
    ∀ words children,
      (words + fields.count false ≤ children ∨ children + fields.count true ≤ words) →
      (treeFieldLocs fields words children).Nodup := by
  induction fields with
  | nil => intros; exact List.nodup_nil
  | cons bit rest ih =>
    intro words children hApart
    cases bit <;> simp only [treeFieldLocs, List.nodup_cons]
    · refine ⟨fun hMem => ?_, ih _ _ ?_⟩
      · rw [treeFieldLocs_mem] at hMem
        simp [List.count_cons] at hApart
        omega
      · simp [List.count_cons] at hApart
        omega
    · refine ⟨fun hMem => ?_, ih _ _ ?_⟩
      · rw [treeFieldLocs_mem] at hMem
        simp [List.count_cons] at hApart
        omega
      · simp [List.count_cons] at hApart
        omega

end Verified
