import Project.EulerRiemann.FrozenNumericsComponentResidual
import Project.EulerRiemann.FrozenExecutionScalar

namespace Project.EulerRiemann.Frozen.ComponentResidual
open Wasm CodeLib.IEEE64
open Project.ProofKit.F64RusanovResidual
open Project.EulerDynamicFlux.Model (componentCheckedBits)

def Behavior (alpha fluxL fluxR stateL stateR : UInt64) : Prop :=
  let output := componentCheckedBits alpha fluxL fluxR stateL stateR
  output.status = 0 →
    Certificate 0x3FE0000000000000 alpha fluxL fluxR stateL stateR output.value ∧
    |residual 0x3FE0000000000000 alpha fluxL fluxR stateL stateR output.value| ≤
      errorBound 0x3FE0000000000000 alpha fluxL fluxR stateL stateR output.value

def SpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (alpha fluxL fluxR stateL stateR : UInt64),
    TerminatesWith env m 46 initial [.i64 stateR, .i64 stateL, .i64 fluxR, .i64 fluxL, .i64 alpha]
      (fun final values => final = initial ∧
        values = Project.EulerDynamicFlux.Execution.componentValues alpha fluxL fluxR stateL stateR ∧
        Behavior alpha fluxL fluxR stateL stateR)

theorem component_residual : SpecFor Project.EulerRiemann.Frozen.module := by
  intro env initial alpha fluxL fluxR stateL stateR
  refine TerminatesWith.mono (Execution.component_exact env initial alpha fluxL fluxR stateL stateR) ?_
  rintro final values ⟨hFinal, hValues⟩
  refine ⟨hFinal, hValues, ?_⟩
  intro h
  exact ⟨Numerics.accepted_component_certificate alpha fluxL fluxR stateL stateR h,
    Numerics.accepted_component_residual_bound alpha fluxL fluxR stateL stateR h⟩

#print axioms component_residual

end Project.EulerRiemann.Frozen.ComponentResidual
