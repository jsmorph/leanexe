import Project.ProofKit.F32Add

namespace Project.ProofKit.F32Sub
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing
open CodeLib.IEEE32

theorem sign_apply_neg (s : Sign) (z : Int) : (-s).apply z = -(s.apply z) := by
  cases s with
  | negative => exact (neg_neg z).symm
  | positive => rfl

theorem unpacked_sub (a b : UnpackedFloat) :
    UnpackedFloat.sub Format.binary32 a b = UnpackedFloat.add Format.binary32 a b.neg := by
  cases a <;> cases b <;>
    simp [UnpackedFloat.sub, UnpackedFloat.add, UnpackedFloat.neg, sign_apply_neg, sub_eq_add_neg]

theorem decode_negate (x : UInt32) : decode (Wasm.IEEE32.negate x) = (decode x).neg := by
  have he : Wasm.IEEE32.exponent (Wasm.IEEE32.negate x) = Wasm.IEEE32.exponent x := by
    exact exponent_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x)
  have hf : Wasm.IEEE32.fraction (Wasm.IEEE32.negate x) = Wasm.IEEE32.fraction x := by
    exact fraction_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x)
  have hs : sourceSign (Wasm.IEEE32.negate x) = -(sourceSign x) := by
    have h := sign_encodeFinite (!Wasm.IEEE32.sign x) _ _ (exponent_lt x) (fraction_lt x)
    change Wasm.IEEE32.sign (Wasm.IEEE32.negate x) = !Wasm.IEEE32.sign x at h
    unfold sourceSign
    rw [h]
    cases Wasm.IEEE32.sign x <;> rfl
  by_cases he255 : Wasm.IEEE32.exponent x = 255 <;>
    by_cases he0 : Wasm.IEEE32.exponent x = 0 <;>
    by_cases hf0 : Wasm.IEEE32.fraction x = 0 <;>
    simp [decode, he, hf, hs, he255, he0, hf0, UnpackedFloat.neg]

theorem sub_eq (a b : UInt32) : LeanExe.Float32.subBits a b = Wasm.IEEE32.sub a b := by
  rw [sub_unpacked, unpacked_sub, ← decode_negate, ← add_unpacked, F32Add.add_eq]
  rfl

#print axioms sub_eq

end Project.ProofKit.F32Sub
