import Project.EulerRiemann.InitialModel

namespace Project.EulerRiemann.Initial

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

theorem bottomLeft_eq : bottomLeft =
    ⟨0x3FC1A9FBE76C8B44, 0x3FC54D834091C088,
      0x3FC54D834091C088, 0x3FD17C4EE39B78F5⟩ := by decide

theorem bottomRight_eq : bottomRight =
    ⟨0x3FE1089A02752546, 0, 0x3FE48AE2B2115FA4, 0x3FF2318DD21A7C73⟩ := by decide

theorem topLeft_eq : topLeft =
    ⟨0x3FE1089A02752546, 0x3FE48AE2B2115FA4, 0, 0x3FF2318DD21A7C73⟩ := by decide

theorem topRight_eq : topRight =
    ⟨0x3FF8000000000000, 0, 0, 0x400E000000000000⟩ := by decide

#print axioms bottomLeft_eq
#print axioms bottomRight_eq
#print axioms topLeft_eq
#print axioms topRight_eq

end Project.EulerRiemann.Initial
