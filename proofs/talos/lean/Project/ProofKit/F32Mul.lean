import Project.ProofKit.F32MulFinite
import Project.ProofKit.F32Add

namespace Project.ProofKit.F32Mul
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing F32Decoded F32MulFinite
open F32Add (decode_infinite decode_zero exponent_ne)

theorem source_nan_right (a b : UInt32) (hb : Wasm.IEEE32.isNaN b = true) :
    LeanExe.Float32.mulBits a b = Wasm.IEEE32.canonicalNaN := by
  rw [mul_unpacked, decode_nan b hb]
  cases decode a <;> exact pack_nan

theorem mul_eq (a b : UInt32) : LeanExe.Float32.mulBits a b = Wasm.IEEE32.mul a b := by
  by_cases hna : Wasm.IEEE32.isNaN a = true
  · rw [mul_unpacked, decode_nan a hna]
    simp [UnpackedFloat.mul, pack_nan, Wasm.IEEE32.mul, hna]
  by_cases hnb : Wasm.IEEE32.isNaN b = true
  · rw [source_nan_right a b hnb]
    simp [Wasm.IEEE32.mul, hnb]
  have hna' : Wasm.IEEE32.isNaN a = false := Bool.eq_false_iff.mpr hna
  have hnb' : Wasm.IEEE32.isNaN b = false := Bool.eq_false_iff.mpr hnb
  by_cases hia : Wasm.IEEE32.isInfinite a = true
  · rw [mul_unpacked, decode_infinite a hia]
    by_cases hzb : Wasm.IEEE32.scaledMagnitude b = 0
    · rw [decode_zero b hzb]
      simp [UnpackedFloat.mul, pack_nan, Wasm.IEEE32.mul, hna', hnb', hia, hzb]
    · by_cases hib : Wasm.IEEE32.isInfinite b = true
      · rw [decode_infinite b hib]
        simp [UnpackedFloat.mul, pack_infinity, negative_mul, negative_sourceSign,
          Wasm.IEEE32.mul, hna', hnb', hia, hzb]
      · have hib' : Wasm.IEEE32.isInfinite b = false := Bool.eq_false_iff.mpr hib
        rw [decode_finite b (exponent_ne b hnb' hib') hzb]
        simp [UnpackedFloat.mul, pack_infinity, negative_mul, negative_sourceSign,
          Wasm.IEEE32.mul, hna', hnb', hia, hzb]
  have hia' : Wasm.IEEE32.isInfinite a = false := Bool.eq_false_iff.mpr hia
  have hea := exponent_ne a hna' hia'
  by_cases hib : Wasm.IEEE32.isInfinite b = true
  · rw [mul_unpacked, decode_infinite b hib]
    by_cases hza : Wasm.IEEE32.scaledMagnitude a = 0
    · rw [decode_zero a hza]
      simp [UnpackedFloat.mul, pack_nan, Wasm.IEEE32.mul, hna', hnb', hia', hib, hza]
    · rw [decode_finite a hea hza]
      simp [UnpackedFloat.mul, pack_infinity, negative_mul, negative_sourceSign,
        Wasm.IEEE32.mul, hna', hnb', hia', hib, hza]
  have hib' : Wasm.IEEE32.isInfinite b = false := Bool.eq_false_iff.mpr hib
  have heb := exponent_ne b hnb' hib'
  by_cases hza : Wasm.IEEE32.scaledMagnitude a = 0
  · rw [mul_unpacked, decode_zero a hza]
    by_cases hzb : Wasm.IEEE32.scaledMagnitude b = 0
    · rw [decode_zero b hzb]
      simp [UnpackedFloat.mul, pack_zero, negative_mul, negative_sourceSign,
        Wasm.IEEE32.mul, hna', hnb', hia', hib', hza]
    · rw [decode_finite b heb hzb]
      simp [UnpackedFloat.mul, pack_zero, negative_mul, negative_sourceSign,
        Wasm.IEEE32.mul, hna', hnb', hia', hib', hza]
  · by_cases hzb : Wasm.IEEE32.scaledMagnitude b = 0
    · rw [mul_unpacked, decode_finite a hea hza, decode_zero b hzb]
      simp [UnpackedFloat.mul, pack_zero, negative_mul, negative_sourceSign,
        Wasm.IEEE32.mul, hna', hnb', hia', hib', hzb]
    · exact mul_eq_talos_finite a b hea heb hza hzb

#print axioms mul_eq

end Project.ProofKit.F32Mul
