import Project.ProofKit.F64OutwardSpec

namespace Project.ProofKit.F64Outward
set_option exponentiation.threshold 4096

theorem signed_zero_endpoints :
    endpoint true 0 = ⟨0, 1⟩ ∧
    endpoint true 0x8000000000000000 = ⟨0, 1⟩ ∧
    endpoint false 0 = ⟨0, 0x8000000000000001⟩ ∧
    endpoint false 0x8000000000000000 = ⟨0, 0x8000000000000001⟩ := by decide +kernel

theorem range_rejection :
    endpoint true 0x7FEFFFFFFFFFFFFF = rejected ∧
    endpoint false 0xFFEFFFFFFFFFFFFF = rejected ∧
    endpoint true 0x7FF0000000000000 = rejected ∧
    endpoint false 0xFFF0000000000000 = rejected ∧
    endpoint true 0x7FF8000000000000 = rejected := by decide +kernel

theorem division_zero_rejection :
    div true 0x3FF0000000000000 0 = rejected ∧
    div true 0x3FF0000000000000 0x8000000000000000 = rejected ∧
    div false 0x3FF0000000000000 0 = rejected ∧
    div false 0x3FF0000000000000 0x8000000000000000 = rejected := by decide +kernel

theorem square_root_boundary :
    sqrt true 0xBFF0000000000000 = rejected ∧
    sqrt false 0xBFF0000000000000 = rejected ∧
    sqrt true 0x8000000000000000 = ⟨0, 1⟩ ∧
    sqrt false 0x8000000000000000 = ⟨0, 0x8000000000000001⟩ := by decide +kernel

theorem rounded_underflow :
    mul true 1 0x3FE0000000000000 = ⟨0, 1⟩ ∧
    mul false 1 0x3FE0000000000000 = ⟨0, 0x8000000000000001⟩ := by decide +kernel

theorem exact_sum_endpoints :
    add true 0x3FF0000000000000 0x3FF0000000000000 = ⟨0, 0x4000000000000001⟩ ∧
    add false 0x3FF0000000000000 0x3FF0000000000000 = ⟨0, 0x3FFFFFFFFFFFFFFF⟩ := by decide +kernel

#print axioms signed_zero_endpoints
#print axioms range_rejection
#print axioms division_zero_rejection
#print axioms square_root_boundary
#print axioms rounded_underflow
#print axioms exact_sum_endpoints
end Project.ProofKit.F64Outward
