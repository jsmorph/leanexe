import Project.EulerRiemann.ReconstructionSafety

namespace Project.EulerRiemann.Reconstruction
open Project.Euler2DCellStep.Sweep (State)
set_option exponentiation.threshold 4096

def testLeft : State := ⟨0x3FF0000000000000, 0, 0, 0x3FC0000000000000⟩
def testCenter : State := ⟨0x3FF0000000000000, 0x3FF0000000000000, 0, 0x3FE4000000000000⟩
def testRight : State := ⟨0x3FF0000000000000, 0x4000000000000000, 0, 0x4001000000000000⟩

theorem unrestricted_counterexample_rejected :
    candidate testCenter (slope testLeft testCenter testRight).state
      0x3FE0000000000000 = rejectedFaces := by decide +kernel

theorem second_counterexample_rejected :
    candidate testCenter (slope testLeft testCenter testRight).state
      0x3FD0000000000000 = rejectedFaces := by decide +kernel

theorem counterexample_limited :
    reconstruct 3 testLeft testCenter testRight =
      ⟨0, ⟨0x3FF0000000000000, 0x3FEC000000000000, 0, 0x3FE2000000000000⟩,
       ⟨0x3FF0000000000000, 0x3FF2000000000000, 0, 0x3FE6000000000000⟩,
       0x3FC0000000000000⟩ := by decide +kernel

theorem zero_budget_constant :
    reconstruct 0 testLeft testCenter testRight = constantFaces testCenter := by decide +kernel

theorem invalid_input_rejected :
    reconstruct 3 zeroState testCenter testRight = rejectedFaces ∧
    reconstruct 3 testLeft ⟨0x8000000000000000, 0, 0, 0x3FF0000000000000⟩ testRight =
      rejectedFaces := by decide +kernel

theorem nonfinite_input_rejected :
    reconstruct 3 testLeft testCenter ⟨0x3FF0000000000000, 0x7FF8000000000000, 0,
      0x3FF0000000000000⟩ = rejectedFaces := by decide +kernel

#print axioms counterexample_limited
#print axioms zero_budget_constant
#print axioms invalid_input_rejected
#print axioms nonfinite_input_rejected

end Project.EulerRiemann.Reconstruction
