import LeanExe.ProofKit.F64AddFinite

namespace LeanExe.ProofKit.F64Decoded
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing F64AddFinite FloatCommon

def mantissa (x : UInt64) : Nat :=
  if Wasm.IEEE64.exponent x = 0 then Wasm.IEEE64.fraction x
  else 2 ^ 52 + Wasm.IEEE64.fraction x

def exponent (x : UInt64) : Int :=
  if Wasm.IEEE64.exponent x = 0 then -1074 else (Wasm.IEEE64.exponent x : Int) - 1075

theorem exponent_ge (x : UInt64) : -1074 ≤ exponent x := by
  unfold exponent
  split <;> omega

theorem scaled_mantissa (x : UInt64) :
    mantissa x * 2 ^ (exponent x + 1074).toNat = Wasm.IEEE64.scaledMagnitude x := by
  by_cases he : Wasm.IEEE64.exponent x = 0
  · simp [mantissa, exponent, Wasm.IEEE64.scaledMagnitude, he]
  · have hk : ((Wasm.IEEE64.exponent x : Int) - 1075 + 1074).toNat =
        Wasm.IEEE64.exponent x - 1 := by omega
    simp only [mantissa, exponent, he, ↓reduceIte, hk, Wasm.IEEE64.scaledMagnitude,
      beq_iff_eq]

theorem scaled_value (x : UInt64) :
    scaled (sourceSign x) (mantissa x) (exponent x) = Wasm.IEEE64.scaledValue x := by
  unfold scaled
  rw [scaled_mantissa]
  unfold sourceSign Wasm.IEEE64.scaledValue
  cases Wasm.IEEE64.sign x <;> rfl

theorem mantissa_pos (x : UInt64) (hx : Wasm.IEEE64.scaledMagnitude x ≠ 0) :
    0 < mantissa x := by
  have h := scaled_mantissa x
  by_contra hn
  have hm : mantissa x = 0 := by omega
  rw [hm, Nat.zero_mul] at h
  exact hx h.symm

theorem decode_finite (x : UInt64) (he : Wasm.IEEE64.exponent x ≠ 2047)
    (hx : Wasm.IEEE64.scaledMagnitude x ≠ 0) :
    decode x = .finite (sourceSign x) (mantissa x) (exponent x) (mantissa_pos x hx) := by
  unfold decode
  simp only [he, ↓reduceIte]
  by_cases he0 : Wasm.IEEE64.exponent x = 0
  · have hf : Wasm.IEEE64.fraction x ≠ 0 := by
      simpa [Wasm.IEEE64.scaledMagnitude, he0] using hx
    simp [he0, hf, mantissa, exponent]
  · simp [he0, mantissa, exponent]

theorem finite_add (a b : UInt64)
    (hea : Wasm.IEEE64.exponent a ≠ 2047) (heb : Wasm.IEEE64.exponent b ≠ 2047)
    (ha : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    LeanExe.Float64.addBits a b =
      roundedSigned (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b) := by
  rw [add_unpacked, decode_finite a hea ha, decode_finite b heb hb,
    pack_add_finite _ _ _ _ _ _ _ _ (exponent_ge a) (exponent_ge b), scaled_value, scaled_value]

theorem target_exponent (x : UInt64) (hx : Wasm.IEEE64.scaledMagnitude x ≠ 0) :
    Format.binary64.targetExponent (totalExponent (mantissa x) (exponent x)) = exponent x := by
  have hf := F64Source.fraction_lt x
  by_cases he : Wasm.IEEE64.exponent x = 0
  · have hm : Wasm.IEEE64.fraction x ≠ 0 := by
      simpa [Wasm.IEEE64.scaledMagnitude, he] using hx
    have hl := (Nat.log2_lt hm).mpr hf
    simp only [mantissa, exponent, he, ↓reduceIte, Format.targetExponent,
      totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  · have hl : (2 ^ 52 + Wasm.IEEE64.fraction x).log2 = 52 := by
      apply (Nat.log2_eq_iff (by omega)).mpr
      constructor <;> omega
    simp only [mantissa, exponent, he, ↓reduceIte, Format.targetExponent,
      totalExponent, Format.mantissaBits, Format.minExponent, hl]
    omega

theorem round_mantissa (x : UInt64) (hx : Wasm.IEEE64.scaledMagnitude x ≠ 0) :
    UnpackedFloat.round Format.binary64 (sourceSign x) (mantissa x) (exponent x) =
      .finite (sourceSign x) (mantissa x) (exponent x) (mantissa_pos x hx) := by
  have ht := target_exponent x hx
  have h := F64RoundScaled.roundWithAccuracy_eq (sourceSign x) (mantissa x) (exponent x)
    .exact 0 (mantissa x) 0 (by simpa using ht) rfl (by simpa using ht) (by simpa using mantissa_pos x hx)
  simpa [UnpackedFloat.round, ht, decreaseExponent] using h

theorem roundScaled_value (x : UInt64) (he : Wasm.IEEE64.exponent x ≠ 2047)
    (hx : Wasm.IEEE64.scaledMagnitude x ≠ 0) :
    Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign x) (Wasm.IEEE64.scaledMagnitude x) = x := by
  have h := F64Normalize.pack_round_above_min (sourceSign x) (mantissa x) (exponent x)
    (Nat.ne_of_gt (mantissa_pos x hx)) (exponent_ge x)
  rw [round_mantissa, ← decode_finite x he hx, pack_decode, negative_sourceSign,
    scaled_mantissa] at h
  · simpa [Wasm.IEEE64.isNaN, he] using h.symm
  · exact hx

theorem roundedSigned_value (x : UInt64) (he : Wasm.IEEE64.exponent x ≠ 2047)
    (hx : Wasm.IEEE64.scaledMagnitude x ≠ 0) :
    roundedSigned (Wasm.IEEE64.scaledValue x) = x := by
  have hv : roundedSigned (Wasm.IEEE64.scaledValue x) =
      Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign x) (Wasm.IEEE64.scaledMagnitude x) := by
    have hp : 0 < Wasm.IEEE64.scaledMagnitude x := Nat.pos_of_ne_zero hx
    have hn : ¬(Wasm.IEEE64.scaledMagnitude x : Int) < 0 := by omega
    cases hs : Wasm.IEEE64.sign x <;>
      simp [roundedSigned, Wasm.IEEE64.scaledValue, hs, hx, hp, hn]
  exact hv.trans (roundScaled_value x he hx)

#print axioms finite_add
#print axioms roundedSigned_value

theorem add_eq_talos_finite (a b : UInt64)
    (hea : Wasm.IEEE64.exponent a ≠ 2047) (heb : Wasm.IEEE64.exponent b ≠ 2047)
    (ha : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    LeanExe.Float64.addBits a b = Wasm.IEEE64.add a b := by
  rw [finite_add a b hea heb ha hb]
  by_cases hz : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = 0
  · have hs : (Wasm.IEEE64.sign a && Wasm.IEEE64.sign b) = false := by
      cases hsa : Wasm.IEEE64.sign a <;> cases hsb : Wasm.IEEE64.sign b <;> try rfl
      simp only [Wasm.IEEE64.scaledValue, hsa, hsb, ↓reduceIte] at hz
      have hp : (0 : Int) < (Wasm.IEEE64.scaledMagnitude a : Int) := by
        exact_mod_cast Nat.pos_of_ne_zero ha
      have hq : (0 : Int) ≤ (Wasm.IEEE64.scaledMagnitude b : Int) := by omega
      omega
    simp [roundedSigned, Wasm.IEEE64.add, Wasm.IEEE64.isNaN, Wasm.IEEE64.isInfinite,
      hea, heb, hz, hs]
  · simp [roundedSigned, Wasm.IEEE64.add, Wasm.IEEE64.isNaN, Wasm.IEEE64.isInfinite,
      hea, heb, hz]

#print axioms add_eq_talos_finite

end LeanExe.ProofKit.F64Decoded
