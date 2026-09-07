import Project.EulerGridStep.Model
import Project.EulerCellStep.Safety

namespace Project.EulerGridStep.Safety
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

@[simp] theorem putCell_size (output : Array UInt64) (index : Nat) (cell : Project.EulerCellStep.Model.CheckedCell) :
    (Model.putCell output index cell).size = output.size := by simp [Model.putCell]

@[simp] theorem advanceAt_size (ratio : UInt64) (input output : Array UInt64) (index : Nat) :
    (Model.advanceAt ratio input output index).size = output.size := by
  unfold Model.advanceAt
  dsimp only
  split <;> simp

@[simp] theorem fill_size (ratio : UInt64) (input output : Array UInt64) (index fuel : Nat) :
    (Model.fill ratio input index output fuel).size = output.size := by
  induction fuel generalizing index output with
  | zero => rfl
  | succ fuel ih =>
    simp only [Model.fill]
    split <;> simp only [ih, advanceAt_size]

theorem putCell_read_before (output : Array UInt64) (index read : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (h : read < 1 + 6 * index) :
    (Model.putCell output index cell)[read]! = output[read]! := by
  dsimp only [Model.putCell]
  repeat rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]

@[simp] theorem putCell_header (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) :
    (Model.putCell output index cell)[0]! = output[0]! :=
  putCell_read_before output index 0 cell (by omega)

theorem fill_of_rejected (ratio : UInt64) (input output : Array UInt64) (index fuel : Nat)
    (h : output[0]! ≠ 0) : Model.fill ratio input index output fuel = output := by
  cases fuel <;> simp [Model.fill, h]

theorem fill_accepted_header (ratio : UInt64) (input output : Array UInt64) (index fuel : Nat)
    (h : (Model.fill ratio input index output fuel)[0]! = 0) : output[0]! = 0 := by
  by_contra hbad
  rw [fill_of_rejected _ _ _ _ _ hbad] at h
  exact hbad h

theorem advanceAt_accepted (ratio : UInt64) (input output : Array UInt64) (index : Nat)
    (hsize : 0 < output.size) (h : (Model.advanceAt ratio input output index)[0]! = 0) :
    (Model.cellAt ratio input index).status = 0 := by
  unfold Model.advanceAt at h
  dsimp only at h
  generalize Model.cellAt ratio input index = cell at h ⊢
  split at h
  · rename_i hcell
    exact beq_iff_eq.mp hcell
  · rw [Array.getElem!_set!_self _ _ _ hsize] at h
    exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

/-- Acceptance implies that every requested cell computation was accepted. -/
theorem fill_accepted_cells (ratio : UInt64) (input output : Array UInt64) (index fuel : Nat)
    (hsize : 0 < output.size) (h : (Model.fill ratio input index output fuel)[0]! = 0) :
    ∀ offset < fuel, (Model.cellAt ratio input (index + offset)).status = 0 := by
  induction fuel generalizing index output with
  | zero => intro offset ho; omega
  | succ fuel ih =>
    have hhead := fill_accepted_header _ _ _ _ _ h
    simp only [Model.fill, hhead, beq_self_eq_true, ite_true] at h
    have hnext := fill_accepted_header _ _ _ _ _ h
    have hcell := advanceAt_accepted _ _ _ _ hsize hnext
    intro offset ho
    cases offset with
    | zero => simpa using hcell
    | succ offset =>
      have rest := ih (output := Model.advanceAt ratio input output index) (index := index + 1) (by simpa using hsize) h offset (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest

#print axioms fill_accepted_cells
#print axioms putCell_read_before
end Project.EulerGridStep.Safety
