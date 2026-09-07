import Project.EulerConservative.Execution
import Project.EulerConservative.Safety

namespace Project.EulerConservative.Spec
open Wasm
open Project.EulerConservative.Execution

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (rho momentum energy : UInt64),
    TerminatesWith env m 5 initial [.i64 energy, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧ values = resultValues rho momentum energy)

noncomputable def AcceptedSafety (rho momentum energy : UInt64) : Prop :=
  (Model.sideCheckedBits rho momentum energy).status = 0 →
    Project.EulerRusanov.RealConservative.Admissible (Guard.decodedState rho momentum energy) ∧
      ∀ word ∈ Safety.intermediateWords rho momentum energy, CodeLib.IEEE64.Finite word

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (rho momentum energy : UInt64),
    TerminatesWith env m 5 initial [.i64 energy, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧ values = resultValues rho momentum energy ∧
        AcceptedSafety rho momentum energy)

private theorem helperLayout : HelperLayout Project.EulerConservative.«module» := by
  constructor <;> rfl

theorem sideCheckedBits_exact : ExactSpecFor Project.EulerConservative.«module» := by
  intro env initial rho momentum energy
  exact sideCheckedBits_exact_in_module helperLayout rfl env initial rho momentum energy

theorem sideCheckedBits_wat_safe : SafeSpecFor Project.EulerConservative.«module» := by
  intro env initial rho momentum energy
  refine TerminatesWith.mono (sideCheckedBits_exact env initial rho momentum energy) ?_
  rintro final values ⟨rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  intro accepted
  exact ⟨Safety.accepted_admissible rho momentum energy accepted,
    Safety.accepted_intermediates_finite rho momentum energy accepted⟩

#print axioms sideCheckedBits_exact
#print axioms sideCheckedBits_wat_safe
end Project.EulerConservative.Spec
