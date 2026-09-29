import Project.ProofKit.F64Decoded

namespace Project.ProofKit.F64Add
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing F64AddFinite F64Decoded FloatCommon

theorem unpacked_comm (a b : UnpackedFloat) :
    UnpackedFloat.add Format.binary64 a b = UnpackedFloat.add Format.binary64 b a := by
  cases a <;> cases b <;> simp [UnpackedFloat.add, min_comm, Int.add_comm]
  all_goals rename_i s t
  all_goals cases s <;> cases t <;> rfl

theorem source_comm (a b : UInt64) : LeanExe.Float64.addBits a b = LeanExe.Float64.addBits b a := by
  rw [add_unpacked, add_unpacked, unpacked_comm]

theorem decode_infinite (x : UInt64) (hx : Wasm.IEEE64.isInfinite x = true) :
    decode x = .infinity (sourceSign x) := by
  simp only [Wasm.IEEE64.isInfinite, Bool.and_eq_true, beq_iff_eq] at hx
  simp [decode, hx.1, hx.2]

theorem infinite_word (x : UInt64) (hx : Wasm.IEEE64.isInfinite x = true) :
    Wasm.IEEE64.infinity (Wasm.IEEE64.sign x) = x := by
  simp only [Wasm.IEEE64.isInfinite, Bool.and_eq_true, beq_iff_eq] at hx
  simpa [F64Source.infinity_eq_encodeFinite, hx.1, hx.2] using encode_fields x

theorem exponent_ne (x : UInt64) (hn : Wasm.IEEE64.isNaN x = false)
    (hi : Wasm.IEEE64.isInfinite x = false) : Wasm.IEEE64.exponent x ≠ 2047 := by
  intro he
  simp [Wasm.IEEE64.isNaN, Wasm.IEEE64.isInfinite, he] at hn hi
  contradiction

theorem zero_fields (x : UInt64) (hx : Wasm.IEEE64.scaledMagnitude x = 0) :
    Wasm.IEEE64.exponent x = 0 ∧ Wasm.IEEE64.fraction x = 0 := by
  unfold Wasm.IEEE64.scaledMagnitude at hx
  dsimp only at hx
  split at hx
  · simpa using And.intro (beq_iff_eq.mp ‹_›) hx
  · have hp : 0 < (2 ^ 52 + Wasm.IEEE64.fraction x) * 2 ^ (Wasm.IEEE64.exponent x - 1) := by positivity
    omega

theorem decode_zero (x : UInt64) (hx : Wasm.IEEE64.scaledMagnitude x = 0) :
    decode x = .zero (sourceSign x) := by
  obtain ⟨he, hf⟩ := zero_fields x hx
  simp [decode, he, hf]

theorem zero_value (x : UInt64) (hx : Wasm.IEEE64.scaledMagnitude x = 0) :
    Wasm.IEEE64.scaledValue x = 0 := by simp [Wasm.IEEE64.scaledValue, hx]

theorem source_zero_nonzero (a b : UInt64) (ha : Wasm.IEEE64.scaledMagnitude a = 0)
    (he : Wasm.IEEE64.exponent b ≠ 2047) (hb : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    LeanExe.Float64.addBits a b = b := by
  rw [add_unpacked, decode_zero a ha, decode_finite b he hb]
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (.finite (sourceSign b) (mantissa b) (exponent b) (mantissa_pos b hb))) = b
  rw [← decode_finite b he hb, pack_decode]
  simp [Wasm.IEEE64.isNaN, he]

theorem talos_zero_nonzero (a b : UInt64) (ha : Wasm.IEEE64.scaledMagnitude a = 0)
    (he : Wasm.IEEE64.exponent b ≠ 2047) (hb : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    Wasm.IEEE64.add a b = b ∧ Wasm.IEEE64.add b a = b := by
  obtain ⟨hea, _⟩ := zero_fields a ha
  have hz : Wasm.IEEE64.scaledValue b ≠ 0 := by
    unfold Wasm.IEEE64.scaledValue
    split <;> simpa using hb
  have hv := roundedSigned_value b he hb
  simp only [roundedSigned, hz, ite_false] at hv
  simpa [Wasm.IEEE64.add, Wasm.IEEE64.isNaN, Wasm.IEEE64.isInfinite,
    hea, he, zero_value a ha, hz] using And.intro hv hv

theorem source_infinite_finite (a b : UInt64) (ha : Wasm.IEEE64.isInfinite a = true)
    (heb : Wasm.IEEE64.exponent b ≠ 2047) : LeanExe.Float64.addBits a b = a := by
  rw [add_unpacked, decode_infinite a ha]
  by_cases hb : Wasm.IEEE64.scaledMagnitude b = 0
  · rw [decode_zero b hb]
    simpa [UnpackedFloat.add, pack_infinity, negative_sourceSign] using infinite_word a ha
  · rw [decode_finite b heb hb]
    simpa [UnpackedFloat.add, pack_infinity, negative_sourceSign] using infinite_word a ha

theorem source_nan_left (a b : UInt64) (ha : Wasm.IEEE64.isNaN a = true) :
    LeanExe.Float64.addBits a b = Wasm.IEEE64.canonicalNaN := by
  rw [add_unpacked, decode_nan a ha]
  exact pack_nan

theorem add_eq (a b : UInt64) : LeanExe.Float64.addBits a b = Wasm.IEEE64.add a b := by
  by_cases hna : Wasm.IEEE64.isNaN a = true
  · rw [source_nan_left a b hna]
    simp [Wasm.IEEE64.add, hna]
  by_cases hnb : Wasm.IEEE64.isNaN b = true
  · rw [source_comm, source_nan_left b a hnb]
    simp [Wasm.IEEE64.add, hnb]
  have hna' : Wasm.IEEE64.isNaN a = false := Bool.eq_false_iff.mpr hna
  have hnb' : Wasm.IEEE64.isNaN b = false := Bool.eq_false_iff.mpr hnb
  by_cases hia : Wasm.IEEE64.isInfinite a = true
  · by_cases hib : Wasm.IEEE64.isInfinite b = true
    · rw [add_unpacked, decode_infinite a hia, decode_infinite b hib]
      have haw := infinite_word a hia
      have hbw := infinite_word b hib
      cases hsa : Wasm.IEEE64.sign a <;> cases hsb : Wasm.IEEE64.sign b <;>
        simp_all [UnpackedFloat.add, sourceSign, pack_nan, pack_infinity, negative,
          Wasm.IEEE64.add]
    · have hib' : Wasm.IEEE64.isInfinite b = false := Bool.eq_false_iff.mpr hib
      rw [source_infinite_finite a b hia (exponent_ne b hnb' hib')]
      simp [Wasm.IEEE64.add, hna', hnb', hia, hib']
  have hia' : Wasm.IEEE64.isInfinite a = false := Bool.eq_false_iff.mpr hia
  by_cases hib : Wasm.IEEE64.isInfinite b = true
  · rw [source_comm, source_infinite_finite b a hib (exponent_ne a hna' hia')]
    simp [Wasm.IEEE64.add, hna', hnb', hia', hib]
  have hib' : Wasm.IEEE64.isInfinite b = false := Bool.eq_false_iff.mpr hib
  have hea := exponent_ne a hna' hia'
  have heb := exponent_ne b hnb' hib'
  by_cases hza : Wasm.IEEE64.scaledMagnitude a = 0
  · by_cases hzb : Wasm.IEEE64.scaledMagnitude b = 0
    · rw [add_unpacked, decode_zero a hza, decode_zero b hzb]
      cases hsa : Wasm.IEEE64.sign a <;> cases hsb : Wasm.IEEE64.sign b <;>
        simp [UnpackedFloat.add, sourceSign, hsa, hsb, pack_zero, negative,
          Wasm.IEEE64.add, hna', hnb', hia', hib', zero_value a hza, zero_value b hzb,
          Wasm.IEEE64.signMask]
    · exact (source_zero_nonzero a b hza heb hzb).trans (talos_zero_nonzero a b hza heb hzb).1.symm
  · by_cases hzb : Wasm.IEEE64.scaledMagnitude b = 0
    · exact (source_comm a b).trans ((source_zero_nonzero b a hzb hea hza).trans
        (talos_zero_nonzero b a hzb hea hza).2.symm)
    · exact add_eq_talos_finite a b hea heb hza hzb

#print axioms add_eq

end Project.ProofKit.F64Add
