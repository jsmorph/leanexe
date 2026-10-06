import LeanExe.ProofKit.F64Decoded
import LeanExe.ProofKit.F64RoundDyadic

namespace LeanExe.ProofKit.F64MulFinite
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing F64Decoded F64RoundDyadic FloatCommon

theorem product_target (a b : UInt64)
    (ha : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    exponent a + exponent b ≤ Format.binary64.targetExponent
      (totalExponent (mantissa a * mantissa b) (exponent a + exponent b)) := by
  have hma := mantissa_pos a ha
  have hmb := mantissa_pos b hb
  by_cases hm : mantissa a * mantissa b < 2 ^ 52
  · have hea : Wasm.IEEE64.exponent a = 0 := by
      by_contra he
      have hlo : 2 ^ 52 ≤ mantissa a := by simp [mantissa, he]
      nlinarith
    have heb : Wasm.IEEE64.exponent b = 0 := by
      by_contra he
      have hlo : 2 ^ 52 ≤ mantissa b := by simp [mantissa, he]
      nlinarith
    simp only [exponent, hea, heb, ↓reduceIte, Format.targetExponent,
      Format.minExponent, Format.mantissaBits]
    omega
  · have hl : 52 ≤ (mantissa a * mantissa b).log2 :=
      (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos hma hmb))).mpr (by omega)
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits]
    omega

theorem product_scaled (a b : UInt64) :
    (mantissa a * mantissa b) * 2 ^ (exponent a + exponent b + 1074 + (1074 : Nat)).toNat =
      Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b := by
  have hea := exponent_ge a
  have heb := exponent_ge b
  have he : (exponent a + exponent b + 1074 + (1074 : Nat)).toNat =
      (exponent a + 1074).toNat + (exponent b + 1074).toNat := by omega
  rw [he, pow_add, ← scaled_mantissa a, ← scaled_mantissa b]
  ring

theorem mul_eq_talos_finite (a b : UInt64)
    (hea : Wasm.IEEE64.exponent a ≠ 2047) (heb : Wasm.IEEE64.exponent b ≠ 2047)
    (ha : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    LeanExe.ProofKit.Float64.mulBits a b = Wasm.IEEE64.mul a b := by
  rw [mul_unpacked, decode_finite a hea ha, decode_finite b heb hb]
  have ht := product_target a b ha hb
  have hd : (exponent a + exponent b - Format.binary64.targetExponent
      (totalExponent (mantissa a * mantissa b) (exponent a + exponent b))).toNat = 0 := by omega
  have hr : UnpackedFloat.round Format.binary64 (sourceSign a * sourceSign b)
      (mantissa a * mantissa b) (exponent a + exponent b) =
      roundWithAccuracy Format.binary64 (sourceSign a * sourceSign b)
        (mantissa a * mantissa b) (exponent a + exponent b) .exact := by
    simp [UnpackedFloat.round, decreaseExponent, hd]
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (roundWithAccuracy Format.binary64 (sourceSign a * sourceSign b)
      (mantissa a * mantissa b) (exponent a + exponent b) .exact)) = _
  rw [← hr, pack_round_above_dyadic _ _ 1074 _
    (Nat.ne_of_gt (Nat.mul_pos (mantissa_pos a ha) (mantissa_pos b hb)))
    (by have h₁ := exponent_ge a; have h₂ := exponent_ge b; omega),
    product_scaled, negative_mul, negative_sourceSign, negative_sourceSign]
  simp [Wasm.IEEE64.mul, Wasm.IEEE64.isNaN, Wasm.IEEE64.isInfinite, hea, heb, ha, hb]

#print axioms mul_eq_talos_finite

end LeanExe.ProofKit.F64MulFinite
