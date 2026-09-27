import LeanExe.Examples.BeckExact
import Project.Beck.IntegerAdd

namespace Project.Beck.Pivot

open LeanExe.Examples.BeckExact IntegerAdd

def searchStep {α : Type*} (test : α → Bool) (item : α) (_ : Option α × Unit) :
    Id (ForInStep (Option α × Unit)) :=
  if test item then .done (some item, ()) else .yield (none, ())

theorem forIn_find {α : Type*} (items : List α) (test : α → Bool) :
    forIn items (none, ()) (searchStep test) = (items.find? test, ()) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [List.forIn_cons]
    cases found : test head <;> simp [searchStep, found, bind, pure, ih]

theorem source_eq (width rows rank column : ℕ) (matrix : Array Integer) :
    pivotRow width rows rank column matrix =
      ((List.range' rank (rows - rank)).find?
        (fun row => !Integer.isZero matrix[row * width + column]!)).getD rows := by
  simp only [pivotRow, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one]
  change ((forIn (List.range' rank (rows - rank)) (none, ())
    (searchStep (fun row => !Integer.isZero matrix[row * width + column]!))).run).1.getD rows = _
  rw [forIn_find]
  rfl

theorem pivot_correct (width rows rank column : ℕ) (matrix : Array Integer) (bound : rank ≤ rows) :
    let pivot := pivotRow width rows rank column matrix
    rank ≤ pivot ∧ pivot ≤ rows ∧
      (pivot < rows → value matrix[pivot * width + column]! ≠ 0) ∧
      ∀ row, rank ≤ row → row < pivot → value matrix[row * width + column]! = 0 := by
  rw [source_eq]
  cases found : (List.range' rank (rows - rank)).find?
      (fun row => !Integer.isZero matrix[row * width + column]!) with
  | none =>
    simp only [Option.getD_none]
    refine ⟨bound, le_rfl, by omega, ?_⟩
    intro row lower upper
    have zero := List.find?_range'_eq_none.mp found row lower (by omega)
    apply (isZero_correct _).mp
    simpa using zero
  | some pivot =>
    have first := List.find?_range'_eq_some.mp found
    have indices := List.mem_range'_1.mp first.2.1
    simp only [Option.getD_some]
    refine ⟨indices.1, by omega, ?_, ?_⟩
    · intro _ zero
      have flag := (isZero_correct _).mpr zero
      simpa [flag] using first.1
    · intro row lower upper
      apply (isZero_correct _).mp
      simpa using first.2.2 row lower upper

#print axioms pivot_correct

end Project.Beck.Pivot
