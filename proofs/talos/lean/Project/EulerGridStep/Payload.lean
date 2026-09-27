import Project.EulerGridStep.Safety

namespace Project.EulerGridStep.Safety
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem putCell_payload (output : Array UInt64) (index field : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hsize : 1 + 6 * (index + 1) ≤ output.size) (hfield : field < 6) :
    (Model.putCell output index cell)[1 + 6 * index + field]! = (Model.payload cell)[field]! := by
  dsimp only [Model.putCell]
  interval_cases field
  all_goals
    try simp only [Nat.add_zero]
    repeat first
      | rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      | rw [Array.getElem!_set!_self _ _ _ (by simp only [Array.size_set!]; omega)]
    simp [Model.payload]
  change (output.set! (1 + 6 * index) cell.density)[1 + 6 * index]! = cell.density
  exact Array.getElem!_set!_self _ _ _ (by omega)

theorem advanceAt_read_before (ratio : UInt64) (input output : Array UInt64)
    (index read : Nat) (hpos : 0 < read) (h : read < 1 + 6 * index) :
    (Model.advanceAt ratio input output index)[read]! = output[read]! := by
  unfold Model.advanceAt
  dsimp only
  split
  · exact putCell_read_before _ _ _ _ h
  · exact Array.getElem!_set!_ne _ _ _ _ (by omega)

theorem fill_read_before (ratio : UInt64) (input output : Array UInt64)
    (index fuel read : Nat) (hpos : 0 < read) (h : read < 1 + 6 * index) :
    (Model.fill ratio input index output fuel)[read]! = output[read]! := by
  induction fuel generalizing index output with
  | zero => rfl
  | succ fuel ih =>
    simp only [Model.fill]
    split
    · rw [ih _ _ (by omega), advanceAt_read_before _ _ _ _ _ hpos h]
    · rfl

theorem advanceAt_payload (ratio : UInt64) (input output : Array UInt64)
    (index field : Nat) (hsize : 1 + 6 * (index + 1) ≤ output.size)
    (hfield : field < 6) (h : (Model.cellAt ratio input index).status = 0) :
    (Model.advanceAt ratio input output index)[1 + 6 * index + field]! =
      (Model.payload (Model.cellAt ratio input index))[field]! := by
  unfold Model.advanceAt
  dsimp only
  generalize Model.cellAt ratio input index = cell at h ⊢
  simpa only [h, beq_self_eq_true, ite_true] using putCell_payload output index field cell hsize hfield

/-- Every accepted output payload is exactly its checked-cell result. -/
theorem fill_payload (ratio : UInt64) (input output : Array UInt64) (index fuel : Nat)
    (hsize : 1 + 6 * (index + fuel) ≤ output.size)
    (h : (Model.fill ratio input index output fuel)[0]! = 0) :
    ∀ offset < fuel, ∀ field < 6,
      (Model.fill ratio input index output fuel)[1 + 6 * (index + offset) + field]! =
        (Model.payload (Model.cellAt ratio input (index + offset)))[field]! := by
  induction fuel generalizing index output with
  | zero => intro offset ho; omega
  | succ fuel ih =>
    have hhead := fill_accepted_header _ _ _ _ _ h
    simp only [Model.fill, hhead, beq_self_eq_true, ite_true] at h ⊢
    have hnext := fill_accepted_header _ _ _ _ _ h
    have hcell := advanceAt_accepted _ _ _ _ (by omega) hnext
    intro offset ho field hf
    cases offset with
    | zero =>
      simp only [Nat.add_zero]
      rw [fill_read_before _ _ _ _ _ _ (by omega) (by omega)]
      exact advanceAt_payload _ _ _ _ _ (by omega) hf hcell
    | succ offset =>
      have rest := ih (index := index + 1) (output := Model.advanceAt ratio input output index)
        (by simp only [advanceAt_size]; omega) h offset (by omega) field hf
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest

#print axioms putCell_payload
#print axioms fill_payload
end Project.EulerGridStep.Safety
