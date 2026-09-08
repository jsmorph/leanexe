import Project.EulerGridScan.Execution

namespace Project.EulerGridScan.Spec
open Wasm
open Project.EulerGridScan.Execution

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (pointer : UInt64) (input : Array UInt64),
    Project.ProofKit.UInt64Array.At initial pointer input →
    TerminatesWith env m 11 initial [.i64 pointer]
      (fun final values => final = initial ∧ values = resultValues input)

/-- Every accepted scan bounds the checked, rounded speeds of all input cells. -/
noncomputable def AcceptedSafety (input : Array UInt64) : Prop :=
  let result := Project.EulerGridStep.Model.maxSpeedCheckedBits input
  result.status = 0 →
    Project.EulerConservative.Model.positiveBits result.speed = true ∧
    ∀ index < input.size / 3, (Project.EulerGridStep.Scan.stateAt input index).status = 0 ∧
      CodeLib.IEEE64.value (Project.EulerGridStep.Scan.stateAt input index).speed ≤
        CodeLib.IEEE64.value result.speed

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (pointer : UInt64) (input : Array UInt64),
    Project.ProofKit.UInt64Array.At initial pointer input →
    TerminatesWith env m 11 initial [.i64 pointer]
      (fun final values => final = initial ∧ values = resultValues input ∧ AcceptedSafety input)

theorem maxSpeedCheckedBits_exact : ExactSpecFor Project.EulerGridScan.«module» := by
  intro env initial pointer input hArray
  exact maxSpeedCheckedBits_exact_in_module concreteLayout env initial pointer input hArray

theorem maxSpeedCheckedBits_wat_safe : SafeSpecFor Project.EulerGridScan.«module» := by
  intro env initial pointer input hArray
  refine TerminatesWith.mono (maxSpeedCheckedBits_exact env initial pointer input hArray) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, Project.EulerGridStep.Scan.maxSpeed_safe input⟩

#print axioms maxSpeedCheckedBits_exact
#print axioms maxSpeedCheckedBits_wat_safe
end Project.EulerGridScan.Spec
