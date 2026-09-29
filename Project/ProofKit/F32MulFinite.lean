import Project.ProofKit.F32Decoded
import Project.ProofKit.F32RoundDyadic

namespace Project.ProofKit.F32MulFinite
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing F32Decoded F32RoundDyadic

theorem product_target (a b : UInt32)
    (ha : Wasm.IEEE32.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    exponent a + exponent b ≤ Format.binary32.targetExponent
      (totalExponent (mantissa a * mantissa b) (exponent a + exponent b)) := by
  have hma := mantissa_pos a ha
  have hmb := mantissa_pos b hb
  by_cases hm : mantissa a * mantissa b < 2 ^ 23
  · have hea : Wasm.IEEE32.exponent a = 0 := by
      by_contra he
      have hlo : 2 ^ 23 ≤ mantissa a := by simp [mantissa, he]
      nlinarith
    have heb : Wasm.IEEE32.exponent b = 0 := by
      by_contra he
      have hlo : 2 ^ 23 ≤ mantissa b := by simp [mantissa, he]
      nlinarith
    simp only [exponent, hea, heb, ↓reduceIte, Format.targetExponent,
      Format.minExponent, Format.mantissaBits]
    omega
  · have hl : 23 ≤ (mantissa a * mantissa b).log2 :=
      (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos hma hmb))).mpr (by omega)
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits]
    omega

theorem product_scaled (a b : UInt32) :
    (mantissa a * mantissa b) * 2 ^ (exponent a + exponent b + 149 + (149 : Nat)).toNat =
      Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b := by
  have hea := exponent_ge a
  have heb := exponent_ge b
  have he : (exponent a + exponent b + 149 + (149 : Nat)).toNat =
      (exponent a + 149).toNat + (exponent b + 149).toNat := by omega
  rw [he, pow_add, ← scaled_mantissa a, ← scaled_mantissa b]
  ring

theorem negative_mul (a b : Sign) : negative (a * b) = (negative a != negative b) := by
  cases a <;> cases b <;> rfl

theorem mul_eq_talos_finite (a b : UInt32)
    (hea : Wasm.IEEE32.exponent a ≠ 255) (heb : Wasm.IEEE32.exponent b ≠ 255)
    (ha : Wasm.IEEE32.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    LeanExe.Float32.mulBits a b = Wasm.IEEE32.mul a b := by
  rw [mul_unpacked, decode_finite a hea ha, decode_finite b heb hb]
  have ht := product_target a b ha hb
  have hd : (exponent a + exponent b - Format.binary32.targetExponent
      (totalExponent (mantissa a * mantissa b) (exponent a + exponent b))).toNat = 0 := by omega
  have hr : UnpackedFloat.round Format.binary32 (sourceSign a * sourceSign b)
      (mantissa a * mantissa b) (exponent a + exponent b) =
      roundWithAccuracy Format.binary32 (sourceSign a * sourceSign b)
        (mantissa a * mantissa b) (exponent a + exponent b) .exact := by
    simp [UnpackedFloat.round, decreaseExponent, hd]
  change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    (roundWithAccuracy Format.binary32 (sourceSign a * sourceSign b)
      (mantissa a * mantissa b) (exponent a + exponent b) .exact)) = _
  rw [← hr, pack_round_above_dyadic _ _ 149 _
    (Nat.ne_of_gt (Nat.mul_pos (mantissa_pos a ha) (mantissa_pos b hb)))
    (by have h₁ := exponent_ge a; have h₂ := exponent_ge b; omega),
    product_scaled, negative_mul, negative_sourceSign, negative_sourceSign]
  simp [Wasm.IEEE32.mul, Wasm.IEEE32.isNaN, Wasm.IEEE32.isInfinite, hea, heb, ha, hb]

#print axioms mul_eq_talos_finite

end Project.ProofKit.F32MulFinite
