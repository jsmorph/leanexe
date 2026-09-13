import Project.EulerRiemann.NumericsInternal
import Project.ProofKit.F64OrderComplete

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order

theorem internal_guard (rho mx my energy : UInt64)
    (hr : Finite rho) (hx : Finite mx) (hy : Finite my) (he : Finite energy)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : 1 / M ≤ value rho) (bx : |value mx| ≤ M)
    (byy : |value my| ≤ M) (be : |value energy| ≤ M)
    (hmargin : 12 * arithmeticEpsilon * M^3 <
      value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)) :
    let u := Wasm.IEEE64.div mx rho
    let v := Wasm.IEEE64.div my rho
    let tx := Wasm.IEEE64.mul mx u
    let ty := Wasm.IEEE64.mul my v
    let sum := Wasm.IEEE64.add tx ty
    let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 sum
    let internal := Wasm.IEEE64.sub energy kinetic
    (finiteBits u && finiteBits tx && finiteBits v && finiteBits ty &&
      finiteBits sum && finiteBits kinetic && positiveBits internal) = true := by
  obtain ⟨hu, hv, htx, hty, hs, hk, hi, ei, _⟩ :=
    internal_error rho mx my energy hr hx hy he M hM hMmax br bx byy be
  have hpositive := positiveBits_of_finite_value_pos _ hi (by
    have herr := (abs_le.mp ei).1
    linarith only [herr, hmargin])
  dsimp only
  simp only [Bool.and_eq_true_iff, finiteBits_iff]
  exact ⟨⟨⟨⟨⟨⟨hu, htx⟩, hv⟩, hty⟩, hs⟩, hk⟩, hpositive⟩

#print axioms internal_guard
end Project.EulerRiemann.Numerics
