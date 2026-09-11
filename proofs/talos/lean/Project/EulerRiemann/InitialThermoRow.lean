import Project.EulerRiemann.InitialStates

namespace Project.EulerRiemann.Initial
open Project.Euler2DConservative.Model

def sideStatuses (x y : Nat) : UInt64 × UInt64 :=
  let q := weighted x y
  ((sideCheckedBits q.density q.mx q.my q.energy).status,
    (sideCheckedBits q.density q.my q.mx q.energy).status)

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem weighted_sides_0 : ∀ y : Fin 6, sideStatuses 0 y.val = (0, 0) := by
  simp only [sideStatuses, weighted, bottomLeft_eq, bottomRight_eq,
    topLeft_eq, topRight_eq]
  decide +kernel

#print axioms weighted_sides_0

end Project.EulerRiemann.Initial
