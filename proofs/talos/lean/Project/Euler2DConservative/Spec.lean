import Project.Euler2DConservative.Execution
import Project.Euler2DConservative.Outputs

namespace Project.Euler2DConservative.Spec
open Wasm
open Project.Euler2DConservative.Execution

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (rho momentum transverse energy : UInt64),
    TerminatesWith env m 5 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧ values = resultValues rho momentum transverse energy)

noncomputable def AcceptedSafety (rho momentum transverse energy : UInt64) : Prop :=
  (Model.sideCheckedBits rho momentum transverse energy).status = 0 →
    Guard.Admissible (Guard.decodedState rho momentum transverse energy) ∧
      (∀ word ∈ Safety.intermediateWords rho momentum transverse energy, CodeLib.IEEE64.Finite word) ∧
      Model.positiveBits (Model.sideCheckedBits rho momentum transverse energy).pressure = true ∧
      Model.positiveBits (Model.sideCheckedBits rho momentum transverse energy).speed = true

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (rho momentum transverse energy : UInt64),
    TerminatesWith env m 5 initial [.i64 energy, .i64 transverse, .i64 momentum, .i64 rho]
      (fun final values => final = initial ∧ values = resultValues rho momentum transverse energy ∧
        AcceptedSafety rho momentum transverse energy)

private theorem helperLayout : HelperLayout Project.Euler2DConservative.«module» :=
  concreteHelperLayout

theorem sideCheckedBits_exact : ExactSpecFor Project.Euler2DConservative.«module» := by
  intro env initial rho momentum transverse energy
  exact sideCheckedBits_exact_in_module helperLayout rfl env initial rho momentum transverse energy

theorem sideCheckedBits_wat_safe : SafeSpecFor Project.Euler2DConservative.«module» := by
  intro env initial rho momentum transverse energy
  refine TerminatesWith.mono (sideCheckedBits_exact env initial rho momentum transverse energy) ?_
  rintro final values ⟨rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  intro accepted
  exact ⟨Safety.accepted_admissible rho momentum transverse energy accepted,
    Safety.accepted_intermediates_finite rho momentum transverse energy accepted,
    Safety.accepted_outputPositive rho momentum transverse energy accepted⟩

#print axioms sideCheckedBits_exact
#print axioms sideCheckedBits_wat_safe
end Project.Euler2DConservative.Spec
