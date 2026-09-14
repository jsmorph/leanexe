import Project.ProofKit.F64RoundingResidual
import Project.ProofKit.RealProductError

namespace Project.ProofKit.F64ErrorPropagation
open CodeLib.IEEE64
open F64RoundingResidual

theorem add (a b : UInt64) (A B ea eb : ℝ)
    (ha : CodeLib.IEEE64.Finite a) (hb : CodeLib.IEEE64.Finite b)
    (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.add a b))
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) :
    |value (Wasm.IEEE64.add a b) - (A + B)| ≤ radius (Wasm.IEEE64.add a b) + (ea + eb) := by
  have hsum : |value a + value b - (A + B)| ≤ ea + eb := by
    rw [show value a + value b - (A + B) = (value a - A) + (value b - B) by ring]
    exact (abs_add_le _ _).trans (add_le_add hea heb)
  exact (abs_sub_le _ (value a + value b) _).trans
    (add_le_add (add_error a b ha hb hf) hsum)

theorem sub (a b : UInt64) (A B ea eb : ℝ)
    (ha : CodeLib.IEEE64.Finite a) (hb : CodeLib.IEEE64.Finite b)
    (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.sub a b))
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) :
    |value (Wasm.IEEE64.sub a b) - (A - B)| ≤ radius (Wasm.IEEE64.sub a b) + (ea + eb) := by
  have hsum : |value a - value b - (A - B)| ≤ ea + eb := by
    rw [show value a - value b - (A - B) = (value a - A) + -(value b - B) by ring]
    exact (abs_add_le _ _).trans (add_le_add hea (by simpa only [abs_neg] using heb))
  exact (abs_sub_le _ (value a - value b) _).trans
    (add_le_add (sub_error a b ha hb hf) hsum)

theorem mul (a b : UInt64) (A B ea eb : ℝ)
    (ha : CodeLib.IEEE64.Finite a) (hb : CodeLib.IEEE64.Finite b)
    (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.mul a b))
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) :
    |value (Wasm.IEEE64.mul a b) - A * B| ≤
      radius (Wasm.IEEE64.mul a b) + (|value a| * eb + ea * |B|) :=
  (abs_sub_le _ (value a * value b) _).trans
    (add_le_add (mul_error a b ha hb hf)
      (RealProductError.product_error _ _ _ _ _ _ _ _ hea heb le_rfl le_rfl))

#print axioms add
#print axioms sub
#print axioms mul
end Project.ProofKit.F64ErrorPropagation
