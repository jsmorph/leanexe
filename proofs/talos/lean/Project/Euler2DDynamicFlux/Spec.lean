import Project.Euler2DDynamicFlux.Execution
import Project.Euler2DDynamicFlux.Safety

namespace Project.Euler2DDynamicFlux.Spec
open Wasm
open Project.Euler2DDynamicFlux.Execution

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
      (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64),
    TerminatesWith env m 25 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR, .i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL]
      (fun final values => final = initial ∧ values = resultValues rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR)

noncomputable def AcceptedSafety (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64) : Prop :=
  let out := Model.fluxCheckedBits rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR
  out.status = 0 →
    (Project.Euler2DConservative.Guard.Admissible
      (Project.Euler2DConservative.Guard.decodedState rhoL momentumL transverseL energyL) ∧
    Project.Euler2DConservative.Guard.Admissible
      (Project.Euler2DConservative.Guard.decodedState rhoR momentumR transverseR energyR)) ∧
    CodeLib.IEEE64.Finite out.mass ∧ CodeLib.IEEE64.Finite out.momentum ∧
    CodeLib.IEEE64.Finite out.transverse ∧ CodeLib.IEEE64.Finite out.energy ∧ Project.Euler2DConservative.Model.positiveBits out.alpha = true

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
      (rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR : UInt64),
    TerminatesWith env m 25 initial [.i64 energyR, .i64 transverseR, .i64 momentumR, .i64 rhoR, .i64 energyL, .i64 transverseL, .i64 momentumL, .i64 rhoL]
      (fun final values => final = initial ∧ values = resultValues rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR ∧
        AcceptedSafety rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR)

theorem fluxCheckedBits_exact : ExactSpecFor Project.Euler2DDynamicFlux.«module» := by
  intro env initial rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR
  exact fluxCheckedBits_exact_in_module concreteLayout env initial rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR

theorem fluxCheckedBits_wat_safe : SafeSpecFor Project.Euler2DDynamicFlux.«module» := by
  intro env initial rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR
  refine TerminatesWith.mono (fluxCheckedBits_exact env initial rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR) ?_
  rintro final values ⟨rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  intro accepted
  exact ⟨Safety.accepted_admissible _ _ _ _ _ _ _ _ accepted,
    Safety.accepted_fields _ _ _ _ _ _ _ _ accepted⟩

#print axioms fluxCheckedBits_exact
#print axioms fluxCheckedBits_wat_safe
end Project.Euler2DDynamicFlux.Spec
