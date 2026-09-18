import Project.ProofKit.F32DivCore
import Project.ProofKit.F32Add

namespace Project.ProofKit.F32Div
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing F32Decoded F32DivCore
open F32Add (decode_infinite decode_zero exponent_ne)

theorem negative_div (a b : Sign) : negative (a / b) = (negative a != negative b) := by
  cases a <;> cases b <;> rfl

theorem div_eq_talos_finite (a b : UInt32)
    (hea : Wasm.IEEE32.exponent a ≠ 255) (heb : Wasm.IEEE32.exponent b ≠ 255)
    (ha : Wasm.IEEE32.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    LeanExe.Float32.divBits a b = Wasm.IEEE32.div a b := by
  rw [div_unpacked, decode_finite a hea ha, decode_finite b heb hb,
    pack_div_finite _ _ _ _ _ _ _ _ (exponent_ge a) (exponent_ge b),
    scaled_mantissa, scaled_mantissa, negative_div, negative_sourceSign, negative_sourceSign]
  simp [Wasm.IEEE32.div, Wasm.IEEE32.isNaN, Wasm.IEEE32.isInfinite, hea, heb, ha, hb]

theorem source_nan_right (a b : UInt32) (hb : Wasm.IEEE32.isNaN b = true) :
    LeanExe.Float32.divBits a b = Wasm.IEEE32.canonicalNaN := by
  rw [div_unpacked, decode_nan b hb]
  cases decode a <;> exact pack_nan

theorem div_eq (a b : UInt32) : LeanExe.Float32.divBits a b = Wasm.IEEE32.div a b := by
  by_cases hna : Wasm.IEEE32.isNaN a = true
  · rw [div_unpacked, decode_nan a hna]
    simp [UnpackedFloat.div, pack_nan, Wasm.IEEE32.div, hna]
  by_cases hnb : Wasm.IEEE32.isNaN b = true
  · rw [source_nan_right a b hnb]
    simp [Wasm.IEEE32.div, hnb]
  have hna' : Wasm.IEEE32.isNaN a = false := Bool.eq_false_iff.mpr hna
  have hnb' : Wasm.IEEE32.isNaN b = false := Bool.eq_false_iff.mpr hnb
  by_cases hia : Wasm.IEEE32.isInfinite a = true
  · rw [div_unpacked, decode_infinite a hia]
    by_cases hib : Wasm.IEEE32.isInfinite b = true
    · rw [decode_infinite b hib]
      simp [UnpackedFloat.div, pack_nan, Wasm.IEEE32.div, hna', hnb', hia, hib]
    · have hib' : Wasm.IEEE32.isInfinite b = false := Bool.eq_false_iff.mpr hib
      by_cases hzb : Wasm.IEEE32.scaledMagnitude b = 0
      · rw [decode_zero b hzb]
        simp [UnpackedFloat.div, pack_infinity, negative_div, negative_sourceSign,
          Wasm.IEEE32.div, hna', hnb', hia, hib']
      · rw [decode_finite b (exponent_ne b hnb' hib') hzb]
        simp [UnpackedFloat.div, pack_infinity, negative_div, negative_sourceSign,
          Wasm.IEEE32.div, hna', hnb', hia, hib']
  have hia' : Wasm.IEEE32.isInfinite a = false := Bool.eq_false_iff.mpr hia
  have hea := exponent_ne a hna' hia'
  by_cases hib : Wasm.IEEE32.isInfinite b = true
  · rw [div_unpacked, decode_infinite b hib]
    by_cases hza : Wasm.IEEE32.scaledMagnitude a = 0
    · rw [decode_zero a hza]
      simp [UnpackedFloat.div, pack_zero, negative_div, negative_sourceSign,
        Wasm.IEEE32.div, hna', hnb', hia', hib]
    · rw [decode_finite a hea hza]
      simp [UnpackedFloat.div, pack_zero, negative_div, negative_sourceSign,
        Wasm.IEEE32.div, hna', hnb', hia', hib]
  have hib' : Wasm.IEEE32.isInfinite b = false := Bool.eq_false_iff.mpr hib
  have heb := exponent_ne b hnb' hib'
  by_cases hza : Wasm.IEEE32.scaledMagnitude a = 0
  · rw [div_unpacked, decode_zero a hza]
    by_cases hzb : Wasm.IEEE32.scaledMagnitude b = 0
    · rw [decode_zero b hzb]
      simp [UnpackedFloat.div, pack_nan, Wasm.IEEE32.div, hna', hnb', hia', hib', hza, hzb]
    · rw [decode_finite b heb hzb]
      simp [UnpackedFloat.div, pack_zero, negative_div, negative_sourceSign,
        Wasm.IEEE32.div, hna', hnb', hia', hib', hza, hzb]
  · by_cases hzb : Wasm.IEEE32.scaledMagnitude b = 0
    · rw [div_unpacked, decode_finite a hea hza, decode_zero b hzb]
      simp [UnpackedFloat.div, pack_infinity, negative_div, negative_sourceSign,
        Wasm.IEEE32.div, hna', hnb', hia', hib', hza, hzb]
    · exact div_eq_talos_finite a b hea heb hza hzb

#print axioms div_eq

end Project.ProofKit.F32Div
