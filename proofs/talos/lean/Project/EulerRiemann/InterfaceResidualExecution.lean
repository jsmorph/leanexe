import Project.EulerRiemann.NumericsInterfaceResidual
import Project.EulerRiemann.ExecutionFlux

namespace Project.EulerRiemann.InterfaceResidual
open Wasm CodeLib.IEEE64
open Project.Euler2DConservative.Guard (decodedState)

def Behavior (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64) : Prop :=
  let flux := Numerics.fluxCheckedBits rhoL mxL myL energyL rhoR mxR myR energyR
  flux.status = 0 → ∀ i,
    |value (Numerics.fluxWords flux i) - RealRusanov.interfaceFlux (value flux.alpha)
      (decodedState rhoL mxL myL energyL) (decodedState rhoR mxR myR energyR) i| ≤
      Numerics.interfaceErrorBounds rhoL mxL myL energyL rhoR mxR myR energyR i

def SpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64),
    TerminatesWith env m 54 initial
      [.i64 energyR, .i64 myR, .i64 mxR, .i64 rhoR, .i64 energyL, .i64 myL, .i64 mxL, .i64 rhoL]
      (fun final values => final = initial ∧
        values = Execution.fluxValues rhoL mxL myL energyL rhoR mxR myR energyR ∧
        Behavior rhoL mxL myL energyL rhoR mxR myR energyR)

theorem interface_residual : SpecFor Project.EulerRiemann.module := by
  intro env initial rhoL mxL myL energyL rhoR mxR myR energyR
  refine TerminatesWith.mono
    (Execution.flux_exact env initial rhoL mxL myL energyL rhoR mxR myR energyR) ?_
  rintro final values ⟨hFinal, hValues⟩
  exact ⟨hFinal, hValues,
    Numerics.accepted_interface_reference_bound rhoL mxL myL energyL rhoR mxR myR energyR⟩

#print axioms interface_residual
end Project.EulerRiemann.InterfaceResidual
