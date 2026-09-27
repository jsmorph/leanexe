import Project.EulerGridStep.Payload

namespace Project.EulerGridStep.Safety
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem step_accepted_size (ratio : UInt64) (input : Array UInt64)
    (h : (Model.stepCheckedBits ratio input)[0]! = 0) :
    (Model.stepCheckedBits ratio input).size = 1 + 6 * (input.size / 3) := by
  unfold Model.stepCheckedBits at h ⊢
  split at h
  · simp at h
  · simp only [*, Bool.false_eq_true, ite_false, fill_size, Array.size_replicate]

theorem step_accepted_cells (ratio : UInt64) (input : Array UInt64)
    (h : (Model.stepCheckedBits ratio input)[0]! = 0) :
    ∀ index < input.size / 3, (Model.cellAt ratio input index).status = 0 := by
  unfold Model.stepCheckedBits at h
  split at h
  · simp at h
  · simpa only [Nat.zero_add] using fill_accepted_cells ratio input
      (Array.replicate (1 + 6 * (input.size / 3)) 0) 0 (input.size / 3) (by simp) h

theorem step_accepted_payload (ratio : UInt64) (input : Array UInt64)
    (h : (Model.stepCheckedBits ratio input)[0]! = 0) :
    ∀ index < input.size / 3, ∀ field < 6,
      (Model.stepCheckedBits ratio input)[1 + 6 * index + field]! =
        (Model.payload (Model.cellAt ratio input index))[field]! := by
  unfold Model.stepCheckedBits at h ⊢
  split at h
  · simp at h
  · simp only [*, Bool.false_eq_true, ite_false]
    simpa only [Nat.zero_add] using fill_payload ratio input
      (Array.replicate (1 + 6 * (input.size / 3)) 0) 0 (input.size / 3) (by simp) h

noncomputable def CellSafety (cell : Project.EulerCellStep.Model.CheckedCell) : Prop :=
  Project.EulerCellStep.Safety.StateSafety cell.density cell.momentum cell.energy cell.pressure ∧
  Project.EulerConservative.Model.positiveBits cell.alpha = true ∧
  CodeLib.IEEE64.Finite cell.courant ∧ 0 < CodeLib.IEEE64.value cell.courant ∧
    CodeLib.IEEE64.value cell.courant ≤ (1 : ℝ) / 2

noncomputable def OutputSafety (output : Array UInt64) (index : Nat) : Prop :=
  let base := 1 + 6 * index
  Project.EulerCellStep.Safety.StateSafety output[base]! output[base + 1]!
      output[base + 2]! output[base + 3]! ∧
  Project.EulerConservative.Model.positiveBits output[base + 4]! = true ∧
  CodeLib.IEEE64.Finite output[base + 5]! ∧ 0 < CodeLib.IEEE64.value output[base + 5]! ∧
    CodeLib.IEEE64.value output[base + 5]! ≤ (1 : ℝ) / 2

theorem cellAt_safe (ratio : UInt64) (input : Array UInt64) (index : Nat)
    (h : (Model.cellAt ratio input index).status = 0) :
    CellSafety (Model.cellAt ratio input index) := by
  unfold CellSafety
  unfold Model.cellAt at h ⊢
  exact ⟨Project.EulerCellStep.Safety.accepted_state _ _ _ _ _ _ _ _ _ _ h,
    Project.EulerCellStep.Safety.accepted_alpha _ _ _ _ _ _ _ _ _ _ h,
    Project.EulerCellStep.Safety.accepted_courant _ _ _ _ _ _ _ _ _ _ h⟩

theorem outputSafety_of_payload (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (hsafe : CellSafety cell)
    (h : ∀ field < 6, output[1 + 6 * index + field]! = (Model.payload cell)[field]!) :
    OutputSafety output index := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  simp [Model.payload] at h0 h1 h2 h3 h4 h5
  simpa only [CellSafety, OutputSafety, h0, h1, h2, h3, h4, h5] using hsafe

/-- The actual six-word payload of every accepted model output is safe. -/
theorem step_accepted_safe (ratio : UInt64) (input : Array UInt64)
    (h : (Model.stepCheckedBits ratio input)[0]! = 0) :
    ∀ index < input.size / 3, OutputSafety (Model.stepCheckedBits ratio input) index := by
  intro index hi
  exact outputSafety_of_payload _ _ _
    (cellAt_safe ratio input index (step_accepted_cells ratio input h index hi))
    (step_accepted_payload ratio input h index hi)

#print axioms step_accepted_size
#print axioms step_accepted_cells
#print axioms step_accepted_payload
#print axioms step_accepted_safe
end Project.EulerGridStep.Safety
