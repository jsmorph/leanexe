import Project.ProofKit.F32SqrtFinite
import Project.ProofKit.F32Add

namespace Project.ProofKit.F32Sqrt
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing F32Decoded F32SqrtFinite
open F32Add (decode_infinite decode_zero exponent_ne)

theorem mantissa_log_le (x : UInt32) (hx : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    (mantissa x).log2 ≤ 23 := by
  have hm := mantissa_pos x hx
  have hf := CodeLib.IEEE32.fraction_lt x
  have hu : mantissa x < 2 ^ 24 := by unfold mantissa; split <;> omega
  have := (Nat.log2_lt (Nat.ne_of_gt hm)).mpr hu
  omega

theorem sqrt_eq (a : UInt32) : LeanExe.Float32.sqrtBits a = Wasm.IEEE32.sqrt a := by
  by_cases hna : Wasm.IEEE32.isNaN a = true
  · rw [sqrt_unpacked, decode_nan a hna]
    simp [UnpackedFloat.sqrt, pack_nan, Wasm.IEEE32.sqrt, hna]
  have hna' : Wasm.IEEE32.isNaN a = false := Bool.eq_false_iff.mpr hna
  by_cases hza : Wasm.IEEE32.scaledMagnitude a = 0
  · have hp := pack_decode a
    rw [decode_zero a hza] at hp
    rw [sqrt_unpacked, decode_zero a hza]
    simpa [UnpackedFloat.sqrt, Wasm.IEEE32.sqrt, hna', hza] using hp
  by_cases hia : Wasm.IEEE32.isInfinite a = true
  · rw [sqrt_unpacked, decode_infinite a hia]
    have hi := F32Add.infinite_word a hia
    cases hs : Wasm.IEEE32.sign a
    · simpa [sourceSign, hs, UnpackedFloat.sqrt, pack_infinity, negative,
        Wasm.IEEE32.sqrt, hna', hza, hia] using hi
    · simp [sourceSign, hs, UnpackedFloat.sqrt, pack_nan, Wasm.IEEE32.sqrt, hna', hza]
  have hia' : Wasm.IEEE32.isInfinite a = false := Bool.eq_false_iff.mpr hia
  have hea := exponent_ne a hna' hia'
  rw [sqrt_unpacked, decode_finite a hea hza]
  cases hs : Wasm.IEEE32.sign a
  · have hsign : sourceSign a = .positive := by simp [sourceSign, hs]
    rw [hsign, pack_sqrt_finite _ _ _ (mantissa_log_le a hza) (exponent_ge a), scaled_mantissa]
    simp [Wasm.IEEE32.sqrt, hna', hza, hia', hs]
  · simp [sourceSign, hs, UnpackedFloat.sqrt, pack_nan, Wasm.IEEE32.sqrt, hna', hza]

#print axioms sqrt_eq

end Project.ProofKit.F32Sqrt
