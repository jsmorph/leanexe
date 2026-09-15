import Project.EulerReconstructed.Scalars
import Project.EulerRiemann.ReconstructedStep

namespace Project.EulerReconstructed.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerReconstruction.Execution (stateValues facesValues)
open Project.EulerOutwardFaceStep.Execution (arguments cellValues)
open Project.EulerRiemann.Reconstruction (reconstruct)
open Project.EulerRiemann.OutwardNumerics (reconstructedStepCheckedBits)

set_option maxRecDepth 32768

set_option maxHeartbeats 800000 in
theorem reconstructed_step_exact (env : HostEnv Unit) (initial : Store Unit)
    (fuel ratio : UInt64) (farLeft left center right farRight : State) :
    TerminatesWith env Project.EulerReconstructed.«module» 108 initial
      (stateValues farRight ++ stateValues right ++ stateValues center ++
        stateValues left ++ stateValues farLeft ++ [.i64 ratio, .i64 fuel])
      (fun final values => final = initial ∧ values = cellValues
        (reconstructedStepCheckedBits fuel.toNat ratio farLeft left center right farRight)) := by
  unfold stateValues
  refine TerminatesWith.of_wp_entry_for (f := func108Def) rfl ?_ (by decide)
  change wp Project.EulerReconstructed.«module» func108 _ initial
    (func108Def.toLocals [.i64 fuel, .i64 ratio,
      .i64 farLeft.density, .i64 farLeft.mx, .i64 farLeft.my, .i64 farLeft.energy,
      .i64 left.density, .i64 left.mx, .i64 left.my, .i64 left.energy,
      .i64 center.density, .i64 center.mx, .i64 center.my, .i64 center.energy,
      .i64 right.density, .i64 right.mx, .i64 right.my, .i64 right.energy,
      .i64 farRight.density, .i64 farRight.mx, .i64 farRight.my, .i64 farRight.energy]) env
  unfold func108
  wp_run [func108Def]
  guard_peel
  reconstruction_call (reconstruct_exact env initial fuel farLeft left center)
  reconstruction_call (reconstruct_exact env initial fuel left center right)
  reconstruction_call (reconstruct_exact env initial fuel center right farRight)
  by_cases hl : (reconstruct fuel.toNat farLeft left center).status = 0
  · by_cases hc : (reconstruct fuel.toNat left center right).status = 0
    · by_cases hr : (reconstruct fuel.toNat center right farRight).status = 0
      · guard_peel
        refine wp_call_tw (face_step_exact env initial ratio center
          (reconstruct fuel.toNat farLeft left center).right
          (reconstruct fuel.toNat left center right).left
          (reconstruct fuel.toNat left center right).right
          (reconstruct fuel.toNat center right farRight).left) ?_
        rintro st values ⟨hst, rfl⟩
        subst st
        dsimp only [cellValues]
        guard_peel
        simp [reconstructedStepCheckedBits, hl, hc, hr]
      · guard_peel
        guard_call (rejectedCell_exact env initial)
        simp [reconstructedStepCheckedBits, hl, hc, hr, cellValues,
          Project.Euler2DCellStep.Model.rejectedCell]
    · guard_peel
      guard_call (rejectedCell_exact env initial)
      simp [reconstructedStepCheckedBits, hl, hc, cellValues,
        Project.Euler2DCellStep.Model.rejectedCell]
  · guard_peel
    guard_call (rejectedCell_exact env initial)
    simp [reconstructedStepCheckedBits, hl, cellValues,
      Project.Euler2DCellStep.Model.rejectedCell]

#print axioms reconstructed_step_exact
end Project.EulerReconstructed.Execution
