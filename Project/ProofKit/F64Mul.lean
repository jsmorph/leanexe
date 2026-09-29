import Project.ProofKit.F64MulFinite
import Project.ProofKit.F64Add

namespace Project.ProofKit.F64Mul
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing F64Decoded F64MulFinite FloatCommon
open F64Add (decode_infinite decode_zero exponent_ne)

theorem source_nan_right (a b : UInt64) (hb : Wasm.IEEE64.isNaN b = true) :
    LeanExe.Float64.mulBits a b = Wasm.IEEE64.canonicalNaN := by
  rw [mul_unpacked, decode_nan b hb]
  cases decode a <;> exact pack_nan

theorem mul_eq (a b : UInt64) : LeanExe.Float64.mulBits a b = Wasm.IEEE64.mul a b := by
  by_cases hna : Wasm.IEEE64.isNaN a = true
  · rw [mul_unpacked, decode_nan a hna]
    simp [UnpackedFloat.mul, pack_nan, Wasm.IEEE64.mul, hna]
  by_cases hnb : Wasm.IEEE64.isNaN b = true
  · rw [source_nan_right a b hnb]
    simp [Wasm.IEEE64.mul, hnb]
  have hna' : Wasm.IEEE64.isNaN a = false := Bool.eq_false_iff.mpr hna
  have hnb' : Wasm.IEEE64.isNaN b = false := Bool.eq_false_iff.mpr hnb
  by_cases hia : Wasm.IEEE64.isInfinite a = true
  · rw [mul_unpacked, decode_infinite a hia]
    by_cases hzb : Wasm.IEEE64.scaledMagnitude b = 0
    · rw [decode_zero b hzb]
      simp [UnpackedFloat.mul, pack_nan, Wasm.IEEE64.mul, hna', hnb', hia, hzb]
    · by_cases hib : Wasm.IEEE64.isInfinite b = true
      · rw [decode_infinite b hib]
        simp [UnpackedFloat.mul, pack_infinity, negative_mul, negative_sourceSign,
          Wasm.IEEE64.mul, hna', hnb', hia, hzb]
      · have hib' : Wasm.IEEE64.isInfinite b = false := Bool.eq_false_iff.mpr hib
        rw [decode_finite b (exponent_ne b hnb' hib') hzb]
        simp [UnpackedFloat.mul, pack_infinity, negative_mul, negative_sourceSign,
          Wasm.IEEE64.mul, hna', hnb', hia, hzb]
  have hia' : Wasm.IEEE64.isInfinite a = false := Bool.eq_false_iff.mpr hia
  have hea := exponent_ne a hna' hia'
  by_cases hib : Wasm.IEEE64.isInfinite b = true
  · rw [mul_unpacked, decode_infinite b hib]
    by_cases hza : Wasm.IEEE64.scaledMagnitude a = 0
    · rw [decode_zero a hza]
      simp [UnpackedFloat.mul, pack_nan, Wasm.IEEE64.mul, hna', hnb', hia', hib, hza]
    · rw [decode_finite a hea hza]
      simp [UnpackedFloat.mul, pack_infinity, negative_mul, negative_sourceSign,
        Wasm.IEEE64.mul, hna', hnb', hia', hib, hza]
  have hib' : Wasm.IEEE64.isInfinite b = false := Bool.eq_false_iff.mpr hib
  have heb := exponent_ne b hnb' hib'
  by_cases hza : Wasm.IEEE64.scaledMagnitude a = 0
  · rw [mul_unpacked, decode_zero a hza]
    by_cases hzb : Wasm.IEEE64.scaledMagnitude b = 0
    · rw [decode_zero b hzb]
      simp [UnpackedFloat.mul, pack_zero, negative_mul, negative_sourceSign,
        Wasm.IEEE64.mul, hna', hnb', hia', hib', hza]
    · rw [decode_finite b heb hzb]
      simp [UnpackedFloat.mul, pack_zero, negative_mul, negative_sourceSign,
        Wasm.IEEE64.mul, hna', hnb', hia', hib', hza]
  · by_cases hzb : Wasm.IEEE64.scaledMagnitude b = 0
    · rw [mul_unpacked, decode_finite a hea hza, decode_zero b hzb]
      simp [UnpackedFloat.mul, pack_zero, negative_mul, negative_sourceSign,
        Wasm.IEEE64.mul, hna', hnb', hia', hib', hzb]
    · exact mul_eq_talos_finite a b hea heb hza hzb

#print axioms mul_eq

end Project.ProofKit.F64Mul
