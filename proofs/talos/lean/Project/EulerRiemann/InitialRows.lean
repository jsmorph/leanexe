import Project.EulerRiemann.InitialStates

namespace Project.EulerRiemann.Initial

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem weighted_guard_0 : ∀ y : Fin 6,
    let q := weighted 0 y.val
    Project.Euler2DConservative.Model.stateGuard q.density q.mx q.my q.energy = true := by
  simp only [weighted, bottomLeft_eq, bottomRight_eq, topLeft_eq, topRight_eq]
  decide +kernel

#print axioms weighted_guard_0

end Project.EulerRiemann.Initial
