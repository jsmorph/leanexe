import Project.EulerRiemann.Numerics

namespace Project.EulerRiemann.Numerics

theorem side_values_of_accepted (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    let u := Wasm.IEEE64.div mx rho
    let v := Wasm.IEEE64.div my rho
    let tx := Wasm.IEEE64.mul mx u
    let ty := Wasm.IEEE64.mul my v
    let internal := Wasm.IEEE64.sub energy (Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.add tx ty))
    let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
    let sound := Wasm.IEEE64.sqrt (Wasm.IEEE64.mul 0x3FF6666666666666 (Wasm.IEEE64.div pressure rho))
    let speed := Wasm.IEEE64.add (Project.Euler2DConservative.Model.absBits u) sound
    sideCheckedBits rho mx my energy =
      ⟨0, u, pressure, speed, mx, Wasm.IEEE64.add tx pressure, Wasm.IEEE64.mul my u,
        Wasm.IEEE64.mul u (Wasm.IEEE64.add energy pressure)⟩ := by
  unfold sideCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [Project.Euler2DConservative.Model.rejectedSide]

#print axioms side_values_of_accepted
end Project.EulerRiemann.Numerics
