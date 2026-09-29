import Project.ProofKit.F64Add

namespace Project.ProofKit.F64Sub
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing F64Source FloatCommon

theorem unpacked_sub (a b : UnpackedFloat) :
    UnpackedFloat.sub Format.binary64 a b = UnpackedFloat.add Format.binary64 a b.neg := by
  cases a <;> cases b <;>
    simp [UnpackedFloat.sub, UnpackedFloat.add, UnpackedFloat.neg, sign_apply_neg, sub_eq_add_neg]

theorem decode_negate (x : UInt64) : decode (Wasm.IEEE64.negate x) = (decode x).neg := by
  have he : Wasm.IEEE64.exponent (Wasm.IEEE64.negate x) = Wasm.IEEE64.exponent x := by
    exact exponent_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x)
  have hf : Wasm.IEEE64.fraction (Wasm.IEEE64.negate x) = Wasm.IEEE64.fraction x := by
    exact fraction_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x)
  have hs : sourceSign (Wasm.IEEE64.negate x) = -(sourceSign x) := by
    have h := sign_encodeFinite (!Wasm.IEEE64.sign x) _ _ (exponent_lt x) (fraction_lt x)
    change Wasm.IEEE64.sign (Wasm.IEEE64.negate x) = !Wasm.IEEE64.sign x at h
    unfold sourceSign
    rw [h]
    cases Wasm.IEEE64.sign x <;> rfl
  by_cases he255 : Wasm.IEEE64.exponent x = 2047 <;>
    by_cases he0 : Wasm.IEEE64.exponent x = 0 <;>
    by_cases hf0 : Wasm.IEEE64.fraction x = 0 <;>
    simp [decode, he, hf, hs, he255, he0, hf0, UnpackedFloat.neg]

theorem sub_eq (a b : UInt64) : LeanExe.Float64.subBits a b = Wasm.IEEE64.sub a b := by
  rw [sub_unpacked, unpacked_sub, ← decode_negate, ← add_unpacked, F64Add.add_eq]
  rfl

#print axioms sub_eq

end Project.ProofKit.F64Sub
