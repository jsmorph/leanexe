import Project.EulerGridStep.Safety

namespace Project.EulerGridStep.Execution

/-- Remaining cells in the pure recurrence, including immediate rejection. -/
def gridRemaining (ratio : UInt64) (input : Array UInt64) (cells index : Nat) (output : Array UInt64) : Array UInt64 :=
  Model.fill ratio input index output (cells - index)

theorem gridRemaining_done (ratio : UInt64) (input output : Array UInt64) (cells index : Nat)
    (hIndex : index ≤ cells) (hDone : index = cells ∨ output[0]! ≠ 0) :
    gridRemaining ratio input cells index output = output := by
  rcases hDone with rfl | hRejected
  · simp [gridRemaining, Model.fill]
  · exact Safety.fill_of_rejected ratio input output index (cells - index) hRejected

theorem gridRemaining_step (ratio : UInt64) (input output : Array UInt64) (cells index : Nat)
    (hIndex : index < cells) (hStatus : output[0]! = 0) :
    gridRemaining ratio input cells index output =
      gridRemaining ratio input cells (index + 1) (Model.advanceAt ratio input output index) := by
  have hFuel : cells - index = (cells - (index + 1)) + 1 := by omega
  simp only [gridRemaining, hFuel, Model.fill, hStatus, beq_self_eq_true, ite_true]

theorem advanceAt_header (ratio : UInt64) (input output : Array UInt64) (index : Nat)
    (hSize : 0 < output.size) (hStatus : output[0]! = 0) :
    (Model.advanceAt ratio input output index)[0]! =
      if (Model.cellAt ratio input index).status = 0 then 0 else 1 := by
  by_cases h : (Model.cellAt ratio input index).status = 0
  · simp [Model.advanceAt, h, hStatus, Safety.putCell_header]
  · simpa [Model.advanceAt, h] using Array.getElem!_set!_self output 0 1 hSize

#print axioms gridRemaining_done
#print axioms gridRemaining_step
#print axioms advanceAt_header
end Project.EulerGridStep.Execution
