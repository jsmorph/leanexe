import Project.EulerRiemann.InitialThermoRow

namespace Project.EulerRiemann.Initial

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem weighted_sides : ∀ x y : Fin 6, sideStatuses x.val y.val = (0, 0) := by
  intro x
  fin_cases x
  · exact weighted_sides_0
  all_goals
    simp only [sideStatuses, weighted, bottomLeft_eq, bottomRight_eq,
      topLeft_eq, topRight_eq]
    decide +kernel

#print axioms weighted_sides

end Project.EulerRiemann.Initial
