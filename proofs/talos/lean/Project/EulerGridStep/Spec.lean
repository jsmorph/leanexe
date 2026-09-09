import Project.EulerGridStep.GridExecution

namespace Project.EulerGridStep.Spec
open Wasm
open Project.EulerGridStep.Execution

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ratio pointer allocs releases frees : UInt64)
    (base : Nat) (input : Array UInt64),
    GridEntryReady initial pointer input base allocs releases frees →
    TerminatesWith env m 36 initial [.i64 pointer, .i64 ratio]
      (fun final values => ∃ root, values = [.i64 root] ∧
        Project.ProofKit.UInt64Array.At final root (Model.stepCheckedBits ratio input))

noncomputable def AcceptedSafety (ratio : UInt64) (input : Array UInt64) : Prop :=
  let output := Model.stepCheckedBits ratio input
  output[0]! = 0 → output.size = 1 + 6 * (input.size / 3) ∧
    ∀ index < input.size / 3, Safety.OutputSafety output index

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ratio pointer allocs releases frees : UInt64)
    (base : Nat) (input : Array UInt64),
    GridEntryReady initial pointer input base allocs releases frees →
    TerminatesWith env m 36 initial [.i64 pointer, .i64 ratio]
      (fun final values => ∃ root, values = [.i64 root] ∧
        Project.ProofKit.UInt64Array.At final root (Model.stepCheckedBits ratio input) ∧ AcceptedSafety ratio input)

theorem stepCheckedBits_exact : ExactSpecFor Project.EulerGridStep.«module» := by
  intro env initial ratio pointer allocs releases frees base input hReady
  exact stepCheckedBits_exact_in_module concreteLayout env initial ratio pointer allocs releases frees base input hReady

/-- Every accepted returned payload has checked finite/admissible states and rounded Courant at most one half. -/
theorem stepCheckedBits_wat_safe : SafeSpecFor Project.EulerGridStep.«module» := by
  intro env initial ratio pointer allocs releases frees base input hReady
  apply (stepCheckedBits_exact env initial ratio pointer allocs releases frees base input hReady).mono
  rintro final values ⟨root, hValues, hArray⟩
  refine ⟨root, hValues, hArray, ?_⟩
  intro hAccepted
  exact ⟨Safety.step_accepted_size ratio input hAccepted, Safety.step_accepted_safe ratio input hAccepted⟩

#print axioms stepCheckedBits_exact
#print axioms stepCheckedBits_wat_safe
end Project.EulerGridStep.Spec
