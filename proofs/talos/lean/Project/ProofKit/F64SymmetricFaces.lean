import Project.ProofKit.F64RoundingResidual

namespace Project.ProofKit.F64SymmetricFaces
open CodeLib.IEEE64
open Project.ProofKit.F64RoundingResidual
noncomputable section

def Certificate (factor center delta left right : UInt64) : Prop :=
  ∃ scaleError leftError rightError : ℝ,
    value left = value center - value factor * value delta - scaleError + leftError ∧
    value right = value center + value factor * value delta + scaleError + rightError ∧
    |scaleError| ≤ radius (Wasm.IEEE64.mul factor delta) ∧
    |leftError| ≤ radius left ∧ |rightError| ≤ radius right

theorem rounded_faces (factor center delta : UInt64)
    (hf : CodeLib.IEEE64.Finite factor) (hc : CodeLib.IEEE64.Finite center)
    (hd : CodeLib.IEEE64.Finite delta)
    (ho : CodeLib.IEEE64.Finite (Wasm.IEEE64.mul factor delta))
    (hl : CodeLib.IEEE64.Finite (Wasm.IEEE64.sub center (Wasm.IEEE64.mul factor delta)))
    (hr : CodeLib.IEEE64.Finite (Wasm.IEEE64.add center (Wasm.IEEE64.mul factor delta))) :
    Certificate factor center delta
      (Wasm.IEEE64.sub center (Wasm.IEEE64.mul factor delta))
      (Wasm.IEEE64.add center (Wasm.IEEE64.mul factor delta)) := by
  refine ⟨value (Wasm.IEEE64.mul factor delta) - value factor * value delta,
    value (Wasm.IEEE64.sub center (Wasm.IEEE64.mul factor delta)) -
      (value center - value (Wasm.IEEE64.mul factor delta)),
    value (Wasm.IEEE64.add center (Wasm.IEEE64.mul factor delta)) -
      (value center + value (Wasm.IEEE64.mul factor delta)),
    by ring, by ring, mul_error factor delta hf hd ho,
    sub_error _ _ hc ho hl, add_error _ _ hc ho hr⟩

theorem face_errors {factor center delta left right : UInt64}
    (h : Certificate factor center delta left right) :
    |value left - (value center - value factor * value delta)| ≤
      radius (Wasm.IEEE64.mul factor delta) + radius left ∧
    |value right - (value center + value factor * value delta)| ≤
      radius (Wasm.IEEE64.mul factor delta) + radius right := by
  rcases h with ⟨es, el, er, hl, hr, hs, hel, her⟩
  rw [hl, hr]
  have hsl := (abs_le.mp hs).1
  have hsu := (abs_le.mp hs).2
  have hll := (abs_le.mp hel).1
  have hlu := (abs_le.mp hel).2
  have hrl := (abs_le.mp her).1
  have hru := (abs_le.mp her).2
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem average_error {factor center delta left right : UInt64}
    (h : Certificate factor center delta left right) :
    |(value left + value right)/2 - value center| ≤ (radius left + radius right)/2 := by
  rcases h with ⟨es, el, er, hl, hr, _, hel, her⟩
  rw [hl, hr]
  have hll := (abs_le.mp hel).1
  have hlu := (abs_le.mp hel).2
  have hrl := (abs_le.mp her).1
  have hru := (abs_le.mp her).2
  apply abs_le.mpr
  constructor <;> linarith

#print axioms rounded_faces
#print axioms face_errors
#print axioms average_error

end
end Project.ProofKit.F64SymmetricFaces
