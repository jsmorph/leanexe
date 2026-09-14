import Project.EulerOutwardSpeed.Speed
import Project.EulerRiemann.OutwardSpeedSpec

namespace Project.EulerOutwardSpeed.Spec
open Wasm CodeLib.IEEE64
open Project.ProofKit.F64Order (positiveBits)
open Project.Euler2DConservative.Guard (StateBounds decodedState)
open Project.Euler2DConservative.RealFlux (velocity soundSpeed eigenvalues)
open Project.EulerRiemann.OutwardSpeed

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64),
    TerminatesWith env m 36 initial [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = Execution.checkedValues (speedUpper rho mx my energy))

def Behavior (rho mx my energy : UInt64) (values : List Value) : Prop :=
  values = [.i64 0, .i64 1] ∨
    ∃ alpha : UInt64, values = [.i64 alpha, .i64 0] ∧
      StateBounds rho mx my energy ∧ Finite alpha ∧ positiveBits alpha = true ∧
      |velocity (decodedState rho mx my energy)| + soundSpeed (decodedState rho mx my energy) ≤
        value alpha ∧
      ∀ i : Fin 4, |eigenvalues (velocity (decodedState rho mx my energy))
        (soundSpeed (decodedState rho mx my energy)) i| ≤ value alpha

def BehaviorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64),
    TerminatesWith env m 36 initial [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ Behavior rho mx my energy values)

theorem speedUpper_exact : ExactSpecFor module := Execution.speed_exact

theorem speedUpper_behavior : BehaviorSpecFor module := by
  intro env initial rho mx my energy
  refine TerminatesWith.mono (speedUpper_exact env initial rho mx my energy) ?_
  rintro final values ⟨hfinal, rfl⟩
  refine ⟨hfinal, ?_⟩
  rcases speed_result rho mx my energy with hr | hs
  · exact Or.inl (by simp [hr, Execution.checkedValues, Project.ProofKit.F64Outward.rejected])
  · have hb := speed_upper rho mx my energy hs
    exact Or.inr ⟨(speedUpper rho mx my energy).value,
      by simp [Execution.checkedValues, hs], hb.1, hb.2.1,
      speed_positive rho mx my energy hs, hb.2.2, speed_eigenvalue_bound rho mx my energy hs⟩

#print axioms speedUpper_exact
#print axioms speedUpper_behavior
end Project.EulerOutwardSpeed.Spec
