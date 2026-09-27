import Project.EulerCellStep.Execution
import Project.EulerCellStep.Safety

namespace Project.EulerCellStep.Spec
open Wasm
open Project.EulerCellStep.Execution

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
      (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64),
    TerminatesWith env m 25 initial [.i64 energyR, .i64 momentumR, .i64 rhoR, .i64 energy, .i64 momentum, .i64 rho, .i64 energyL, .i64 momentumL, .i64 rhoL, .i64 ratio]
      (fun final values => final = initial ∧ values = resultValues ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR)

noncomputable def AcceptedSafety (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64) : Prop :=
  let out := Model.cellCheckedBits ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR
  out.status = 0 →
    Safety.StateSafety out.density out.momentum out.energy out.pressure ∧
    (CodeLib.IEEE64.Finite out.courant ∧ 0 < CodeLib.IEEE64.value out.courant ∧
      CodeLib.IEEE64.value out.courant ≤ (1 : ℝ) / 2) ∧
    Project.EulerConservative.Model.positiveBits out.alpha = true

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
      (ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR : UInt64),
    TerminatesWith env m 25 initial [.i64 energyR, .i64 momentumR, .i64 rhoR, .i64 energy, .i64 momentum, .i64 rho, .i64 energyL, .i64 momentumL, .i64 rhoL, .i64 ratio]
      (fun final values => final = initial ∧ values = resultValues ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR ∧
        AcceptedSafety ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR)

theorem cellCheckedBits_exact : ExactSpecFor Project.EulerCellStep.«module» := by
  intro env initial ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR
  exact cellCheckedBits_exact_in_module concreteLayout env initial ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR

theorem cellCheckedBits_wat_safe : SafeSpecFor Project.EulerCellStep.«module» := by
  intro env initial ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR
  refine TerminatesWith.mono (cellCheckedBits_exact env initial ratio rhoL momentumL energyL rho momentum energy rhoR momentumR energyR) ?_
  rintro final values ⟨rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  intro accepted
  exact ⟨Safety.accepted_state _ _ _ _ _ _ _ _ _ _ accepted,
    Safety.accepted_courant _ _ _ _ _ _ _ _ _ _ accepted,
    Safety.accepted_alpha _ _ _ _ _ _ _ _ _ _ accepted⟩

#print axioms cellCheckedBits_exact
#print axioms cellCheckedBits_wat_safe
end Project.EulerCellStep.Spec
