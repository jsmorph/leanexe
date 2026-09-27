import Project.EulerRiemann.OutwardMeshSpec

namespace Project.EulerRiemann.OutwardCfl
open Project.ProofKit.F64Outward (rejected)
set_option exponentiation.threshold 4096

theorem ratio_boundary :
    (ratioChecked 0x3FD0000000000000 0x3FF0000000000000 0x3FF0000000000000).status = 0 ∧
    (ratioChecked 0x3FDFFFFFFFFFFFFE 0x3FF0000000000000 0x3FF0000000000000).status = 0 ∧
    ratioChecked 0x3FDFFFFFFFFFFFFF 0x3FF0000000000000 0x3FF0000000000000 = rejected ∧
    ratioChecked 0x3FE0000000000000 0x3FF0000000000000 0x3FF0000000000000 = rejected := by decide +kernel

theorem ratio_invalid :
    ratioChecked 0 0x3FF0000000000000 0x3FF0000000000000 = rejected ∧
    ratioChecked 0x3FD0000000000000 0 0x3FF0000000000000 = rejected ∧
    ratioChecked 0x3FD0000000000000 0x3FF0000000000000 0x7FF0000000000000 = rejected := by decide +kernel

theorem production_grid_spacing :
    (spacingLower 192).status = 0 ∧ (spacingLower 800).status = 0 := by decide +kernel

theorem grid_boundary :
    (gridRatioChecked 192 0x3F30000000000000 0x3FF0000000000000).status = 0 ∧
    (gridRatioChecked 800 0x3F30000000000000 0x3FF0000000000000).status = 0 ∧
    gridRatioChecked 800 0x3F50000000000000 0x3FF0000000000000 = rejected ∧
    gridRatioChecked 801 0x3F30000000000000 0x3FF0000000000000 = rejected := by decide +kernel

#print axioms ratio_boundary
#print axioms ratio_invalid
#print axioms production_grid_spacing
#print axioms grid_boundary
end Project.EulerRiemann.OutwardCfl
