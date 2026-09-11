import Project.EulerRiemann.Geometry
import Project.EulerRiemann.InitialRows

namespace Project.EulerRiemann.Initial
open Project.Euler2DCellStep.Sweep

set_option exponentiation.threshold 4096

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem weighted_guard : ∀ x y : Fin 6,
    let q := weighted x.val y.val
    Project.Euler2DConservative.Model.stateGuard q.density q.mx q.my q.energy = true := by
  intro x
  fin_cases x
  · exact weighted_guard_0
  all_goals
    simp only [weighted, bottomLeft_eq, bottomRight_eq, topLeft_eq, topRight_eq]
    decide +kernel

def initial (n : Nat) : Grid n n := fun j i =>
  weighted (LeanExe.Examples.EulerRiemann.lowerFractionNumerator n i.val)
    (LeanExe.Examples.EulerRiemann.lowerFractionNumerator n j.val)

theorem initial_safe (n : Nat) : GridSafe (initial n) := by
  intro j i
  have hx := Geometry.lowerFractionNumerator_le n i.val
  have hy := Geometry.lowerFractionNumerator_le n j.val
  have hg := weighted_guard
    ⟨LeanExe.Examples.EulerRiemann.lowerFractionNumerator n i.val, by omega⟩
    ⟨LeanExe.Examples.EulerRiemann.lowerFractionNumerator n j.val, by omega⟩
  exact ⟨Project.Euler2DConservative.Guard.stateGuard_spec _ _ _ _ hg,
    Project.Euler2DConservative.Guard.stateGuard_admissible _ _ _ _ hg⟩

#print axioms weighted_guard
#print axioms initial_safe

end Project.EulerRiemann.Initial
