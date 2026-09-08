import Project.EulerGridStep.CellPrefixes

namespace Project.EulerGridStep.Execution

@[simp] theorem putCell_size (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) :
    (Model.putCell output index cell).size = output.size := by
  rw [← cellPrefix_six]
  exact cellPrefix_size output index cell 6

@[simp] theorem advanceAt_size (ratio : UInt64) (input output : Array UInt64) (index : Nat) :
    (Model.advanceAt ratio input output index).size = output.size := by
  dsimp only [Model.advanceAt]
  split <;> simp

@[simp] theorem fill_size (ratio : UInt64) (input output : Array UInt64) (index fuel : Nat) :
    (Model.fill ratio input index output fuel).size = output.size := by
  induction fuel generalizing index output with
  | zero => rfl
  | succ fuel ih =>
      unfold Model.fill
      split <;> simp [ih]

#print axioms putCell_size
#print axioms advanceAt_size
#print axioms fill_size
end Project.EulerGridStep.Execution
