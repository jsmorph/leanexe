import Project.EulerGridStep.GridSetup

namespace Project.EulerGridStep.Execution
open Wasm

theorem initial_grid_frame_facts (ratio pointer : UInt64) (base length : Nat) :
    let frame := initialGridFrame (gridValidEntryFrame ratio pointer length) pointer base length
    frame.params.length = 2 ∧ frame.locals.length = 43 ∧ frame.values = [] ∧
      frame.locals[32]? = some (.i64 (arenaRoot base (1 + 6 * (length / 3)) 0)) := by
  simp [initialGridFrame, initialOutputFrame, initialFreshAllocFrame, initialFreshBumpFrame,
    initialCapacityFrame, initialDimensionsFrame, gridValidEntryFrame,
    grid_guard_params, grid_guard_locals, arena_root_eq_heap]

theorem grid_valid_cells (ratio : UInt64) (input : Array UInt64)
    (h : gridEntryInvalid ratio input.size = false) : 0 < input.size / 3 := by
  have hh : Project.EulerConservative.Model.positiveBits ratio = true ∧
      input.size ≠ 0 ∧ input.size % 3 = 0 := by
    simpa [gridEntryInvalid, and_assoc] using h
  omega

theorem grid_model_valid (ratio : UInt64) (input : Array UInt64)
    (h : gridEntryInvalid ratio input.size = false) :
    Model.stepCheckedBits ratio input =
      Model.fill ratio input 0 (Array.replicate (1 + 6 * (input.size / 3)) 0) (input.size / 3) := by
  change (if gridEntryInvalid ratio input.size then _ else _) = _
  rw [h]
  rfl

#print axioms initial_grid_frame_facts
#print axioms grid_valid_cells
#print axioms grid_model_valid
end Project.EulerGridStep.Execution
