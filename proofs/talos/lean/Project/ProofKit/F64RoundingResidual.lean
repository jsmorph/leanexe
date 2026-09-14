import Project.ProofKit.F64AddEnclosure
import Project.ProofKit.F64MulEnclosure

namespace Project.ProofKit.F64RoundingResidual
open CodeLib.IEEE64
open Project.ProofKit.F64Adjacent
noncomputable section

def radius (word : UInt64) : ℝ :=
  max (value word - value (nextDown word)) (value (nextUp word) - value word)

theorem radius_positive (word : UInt64) (hf : CodeLib.IEEE64.Finite word) :
    0 < radius word :=
  (sub_pos.mpr (nextUp_lt word hf)).trans_le (le_max_right _ _)

theorem enclosure_error (word : UInt64) (exactValue : ℝ)
    (h : value (nextDown word) ≤ exactValue ∧ exactValue ≤ value (nextUp word)) :
    |value word - exactValue| ≤ radius word := by
  have hl := le_max_left (value word - value (nextDown word))
    (value (nextUp word) - value word)
  have hr := le_max_right (value word - value (nextDown word))
    (value (nextUp word) - value word)
  unfold radius
  exact abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

theorem add_error (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.add a b)) :
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ radius (Wasm.IEEE64.add a b) :=
  enclosure_error _ _ (add_enclosure a b ha hb hf)

theorem sub_error (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.sub a b)) :
    |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤ radius (Wasm.IEEE64.sub a b) :=
  enclosure_error _ _ (sub_enclosure a b ha hb hf)

theorem mul_error (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.mul a b)) :
    |value (Wasm.IEEE64.mul a b) - value a * value b| ≤ radius (Wasm.IEEE64.mul a b) :=
  enclosure_error _ _ (mul_enclosure a b ha hb hf)

#print axioms radius_positive
#print axioms add_error
#print axioms sub_error
#print axioms mul_error

end
end Project.ProofKit.F64RoundingResidual
