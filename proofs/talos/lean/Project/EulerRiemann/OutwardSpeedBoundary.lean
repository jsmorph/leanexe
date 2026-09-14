import Project.EulerRiemann.OutwardSpeedSpec

namespace Project.EulerRiemann.OutwardSpeed
open Project.ProofKit.F64Outward (rejected)
set_option exponentiation.threshold 4096

theorem rest_state_accepted :
    (speedUpper 0x3FF0000000000000 0 0 0x3FF0000000000000).status = 0 := by decide +kernel

theorem zero_density_rejected :
    speedUpper 0 0 0 0x3FF0000000000000 = rejected ∧
    speedUpper 0x8000000000000000 0 0 0x3FF0000000000000 = rejected := by decide +kernel

theorem nonfinite_state_rejected :
    speedUpper 0x7FF0000000000000 0 0 0x3FF0000000000000 = rejected ∧
    speedUpper 0x3FF0000000000000 0x7FF8000000000000 0 0x3FF0000000000000 = rejected := by decide +kernel

#print axioms rest_state_accepted
#print axioms zero_density_rejected
#print axioms nonfinite_state_rejected
end Project.EulerRiemann.OutwardSpeed
