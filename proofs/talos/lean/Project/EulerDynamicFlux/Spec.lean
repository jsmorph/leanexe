import Project.EulerDynamicFlux.Execution
import Project.EulerDynamicFlux.Safety

namespace Project.EulerDynamicFlux.Spec
open Wasm
open Project.EulerDynamicFlux.Execution

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
      (rhoL momentumL energyL rhoR momentumR energyR : UInt64),
    TerminatesWith env m 16 initial [.i64 energyR, .i64 momentumR, .i64 rhoR, .i64 energyL, .i64 momentumL, .i64 rhoL]
      (fun final values => final = initial ∧ values = resultValues rhoL momentumL energyL rhoR momentumR energyR)

noncomputable def AcceptedSafety (rhoL momentumL energyL rhoR momentumR energyR : UInt64) : Prop :=
  let out := Model.fluxCheckedBits rhoL momentumL energyL rhoR momentumR energyR
  out.status = 0 →
    (Project.EulerRusanov.RealConservative.Admissible
      (Project.EulerConservative.Guard.decodedState rhoL momentumL energyL) ∧
    Project.EulerRusanov.RealConservative.Admissible
      (Project.EulerConservative.Guard.decodedState rhoR momentumR energyR)) ∧
    CodeLib.IEEE64.Finite out.mass ∧ CodeLib.IEEE64.Finite out.momentum ∧
    CodeLib.IEEE64.Finite out.energy ∧ Project.EulerConservative.Model.positiveBits out.alpha = true

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
      (rhoL momentumL energyL rhoR momentumR energyR : UInt64),
    TerminatesWith env m 16 initial [.i64 energyR, .i64 momentumR, .i64 rhoR, .i64 energyL, .i64 momentumL, .i64 rhoL]
      (fun final values => final = initial ∧ values = resultValues rhoL momentumL energyL rhoR momentumR energyR ∧
        AcceptedSafety rhoL momentumL energyL rhoR momentumR energyR)

theorem fluxCheckedBits_exact : ExactSpecFor Project.EulerDynamicFlux.«module» := by
  intro env initial rhoL momentumL energyL rhoR momentumR energyR
  exact fluxCheckedBits_exact_in_module concreteLayout env initial rhoL momentumL energyL rhoR momentumR energyR

theorem fluxCheckedBits_wat_safe : SafeSpecFor Project.EulerDynamicFlux.«module» := by
  intro env initial rhoL momentumL energyL rhoR momentumR energyR
  refine TerminatesWith.mono (fluxCheckedBits_exact env initial rhoL momentumL energyL rhoR momentumR energyR) ?_
  rintro final values ⟨rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  intro accepted
  exact ⟨Safety.accepted_admissible _ _ _ _ _ _ accepted,
    Safety.accepted_fields _ _ _ _ _ _ accepted⟩

#print axioms fluxCheckedBits_exact
#print axioms fluxCheckedBits_wat_safe
end Project.EulerDynamicFlux.Spec
