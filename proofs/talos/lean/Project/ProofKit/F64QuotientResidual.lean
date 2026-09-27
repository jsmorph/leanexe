import Project.ProofKit.F64RoundingResidual
import Project.ProofKit.F64DivEnclosure

namespace Project.ProofKit.F64RoundingResidual
open CodeLib.IEEE64

theorem div_error (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.div a b)) :
    |value (Wasm.IEEE64.div a b) - value a / value b| ≤ radius (Wasm.IEEE64.div a b) :=
  enclosure_error _ _ (F64Adjacent.div_enclosure a b ha hb hb0 hf)

#print axioms div_error
end Project.ProofKit.F64RoundingResidual
