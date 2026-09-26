import Project.EulerRiemann.FrozenNumericsUpdateResidual
import Project.EulerRiemann.FrozenExecutionScalar

namespace Project.EulerRiemann.Frozen.UpdateResidual
open Wasm CodeLib.IEEE64
open Project.ProofKit.F64ConservativeUpdate
open Project.ProofKit.F64RoundingResidual (radius)
open Project.EulerCellStep.Model (updateCheckedBits)

def Behavior (ratio state fluxL fluxR : UInt64) : Prop :=
  let output := updateCheckedBits ratio state fluxL fluxR
  output.status = 0 →
    Certificate ratio state fluxL fluxR output.value ∧
    value output.value - value state = value ratio * (value fluxL - value fluxR) +
      residual ratio state fluxL fluxR output.value ∧
    |residual ratio state fluxL fluxR output.value| ≤
      |value ratio| * radius (IEEE64.sub fluxR fluxL) +
      radius (IEEE64.mul ratio (IEEE64.sub fluxR fluxL)) + radius output.value

def SpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ratio state fluxL fluxR : UInt64),
    TerminatesWith env m 58 initial [.i64 fluxR, .i64 fluxL, .i64 state, .i64 ratio]
      (fun final values => final = initial ∧
        values = Project.EulerCellStep.Execution.updateValues ratio state fluxL fluxR ∧
        Behavior ratio state fluxL fluxR)

theorem update_residual : SpecFor Project.EulerRiemann.Frozen.module := by
  intro env initial ratio state fluxL fluxR
  refine TerminatesWith.mono (Execution.update_exact env initial ratio state fluxL fluxR) ?_
  rintro final values ⟨hFinal, hValues⟩
  refine ⟨hFinal, hValues, ?_⟩
  intro h
  exact ⟨Numerics.accepted_update_certificate ratio state fluxL fluxR h,
    balance ratio state fluxL fluxR _, Numerics.accepted_update_residual_bound ratio state fluxL fluxR h⟩

#print axioms update_residual

end Project.EulerRiemann.Frozen.UpdateResidual
