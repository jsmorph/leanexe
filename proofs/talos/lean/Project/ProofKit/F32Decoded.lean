import Project.ProofKit.F32AddFinite

namespace Project.ProofKit.F32Decoded
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing F32AddFinite

def mantissa (x : UInt32) : Nat :=
  if Wasm.IEEE32.exponent x = 0 then Wasm.IEEE32.fraction x
  else 2 ^ 23 + Wasm.IEEE32.fraction x

def exponent (x : UInt32) : Int :=
  if Wasm.IEEE32.exponent x = 0 then -149 else (Wasm.IEEE32.exponent x : Int) - 150

theorem exponent_ge (x : UInt32) : -149 ≤ exponent x := by
  unfold exponent
  split <;> omega

theorem scaled_mantissa (x : UInt32) :
    mantissa x * 2 ^ (exponent x + 149).toNat = Wasm.IEEE32.scaledMagnitude x := by
  by_cases he : Wasm.IEEE32.exponent x = 0
  · simp [mantissa, exponent, Wasm.IEEE32.scaledMagnitude, he]
  · have hk : ((Wasm.IEEE32.exponent x : Int) - 150 + 149).toNat =
        Wasm.IEEE32.exponent x - 1 := by omega
    simp only [mantissa, exponent, he, ↓reduceIte, hk, Wasm.IEEE32.scaledMagnitude,
      beq_iff_eq]

theorem scaled_value (x : UInt32) :
    scaled (sourceSign x) (mantissa x) (exponent x) = Wasm.IEEE32.scaledValue x := by
  unfold scaled
  rw [scaled_mantissa]
  unfold sourceSign Wasm.IEEE32.scaledValue
  cases Wasm.IEEE32.sign x <;> rfl

theorem mantissa_pos (x : UInt32) (hx : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    0 < mantissa x := by
  have h := scaled_mantissa x
  by_contra hn
  have hm : mantissa x = 0 := by omega
  rw [hm, Nat.zero_mul] at h
  exact hx h.symm

theorem decode_finite (x : UInt32) (he : Wasm.IEEE32.exponent x ≠ 255)
    (hx : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    decode x = .finite (sourceSign x) (mantissa x) (exponent x) (mantissa_pos x hx) := by
  unfold decode
  simp only [he, ↓reduceIte]
  by_cases he0 : Wasm.IEEE32.exponent x = 0
  · have hf : Wasm.IEEE32.fraction x ≠ 0 := by
      simpa [Wasm.IEEE32.scaledMagnitude, he0] using hx
    simp [he0, hf, mantissa, exponent]
  · simp [he0, mantissa, exponent]

theorem finite_add (a b : UInt32)
    (hea : Wasm.IEEE32.exponent a ≠ 255) (heb : Wasm.IEEE32.exponent b ≠ 255)
    (ha : Wasm.IEEE32.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    LeanExe.Float32.addBits a b =
      roundedSigned (Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b) := by
  rw [add_unpacked, decode_finite a hea ha, decode_finite b heb hb,
    pack_add_finite _ _ _ _ _ _ _ _ (exponent_ge a) (exponent_ge b), scaled_value, scaled_value]

theorem target_exponent (x : UInt32) (hx : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    Format.binary32.targetExponent (totalExponent (mantissa x) (exponent x)) = exponent x := by
  have hf := CodeLib.IEEE32.fraction_lt x
  by_cases he : Wasm.IEEE32.exponent x = 0
  · have hm : Wasm.IEEE32.fraction x ≠ 0 := by
      simpa [Wasm.IEEE32.scaledMagnitude, he] using hx
    have hl := (Nat.log2_lt hm).mpr hf
    simp only [mantissa, exponent, he, ↓reduceIte, Format.targetExponent,
      totalExponent, Format.mantissaBits, Format.minExponent]
    omega
  · have hl : (2 ^ 23 + Wasm.IEEE32.fraction x).log2 = 23 := by
      apply (Nat.log2_eq_iff (by omega)).mpr
      constructor <;> omega
    simp only [mantissa, exponent, he, ↓reduceIte, Format.targetExponent,
      totalExponent, Format.mantissaBits, Format.minExponent, hl]
    omega

theorem round_mantissa (x : UInt32) (hx : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    UnpackedFloat.round Format.binary32 (sourceSign x) (mantissa x) (exponent x) =
      .finite (sourceSign x) (mantissa x) (exponent x) (mantissa_pos x hx) := by
  have ht := target_exponent x hx
  have h := F32RoundScaled.roundWithAccuracy_eq (sourceSign x) (mantissa x) (exponent x)
    .exact 0 (mantissa x) 0 (by simpa using ht) rfl (by simpa using ht) (by simpa using mantissa_pos x hx)
  simpa [UnpackedFloat.round, ht, decreaseExponent] using h

theorem roundScaled_value (x : UInt32) (he : Wasm.IEEE32.exponent x ≠ 255)
    (hx : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    Wasm.IEEE32.roundScaledMagnitude (Wasm.IEEE32.sign x) (Wasm.IEEE32.scaledMagnitude x) = x := by
  have h := F32Normalize.pack_round_above_min (sourceSign x) (mantissa x) (exponent x)
    (Nat.ne_of_gt (mantissa_pos x hx)) (exponent_ge x)
  rw [round_mantissa, ← decode_finite x he hx, pack_decode, negative_sourceSign,
    scaled_mantissa] at h
  · simpa [Wasm.IEEE32.isNaN, he] using h.symm
  · exact hx

theorem roundedSigned_value (x : UInt32) (he : Wasm.IEEE32.exponent x ≠ 255)
    (hx : Wasm.IEEE32.scaledMagnitude x ≠ 0) :
    roundedSigned (Wasm.IEEE32.scaledValue x) = x := by
  have hv : roundedSigned (Wasm.IEEE32.scaledValue x) =
      Wasm.IEEE32.roundScaledMagnitude (Wasm.IEEE32.sign x) (Wasm.IEEE32.scaledMagnitude x) := by
    have hp : 0 < Wasm.IEEE32.scaledMagnitude x := Nat.pos_of_ne_zero hx
    have hn : ¬(Wasm.IEEE32.scaledMagnitude x : Int) < 0 := by omega
    cases hs : Wasm.IEEE32.sign x <;>
      simp [roundedSigned, Wasm.IEEE32.scaledValue, hs, hx, hp, hn]
  exact hv.trans (roundScaled_value x he hx)

#print axioms finite_add
#print axioms roundedSigned_value

theorem add_eq_talos_finite (a b : UInt32)
    (hea : Wasm.IEEE32.exponent a ≠ 255) (heb : Wasm.IEEE32.exponent b ≠ 255)
    (ha : Wasm.IEEE32.scaledMagnitude a ≠ 0) (hb : Wasm.IEEE32.scaledMagnitude b ≠ 0) :
    LeanExe.Float32.addBits a b = Wasm.IEEE32.add a b := by
  rw [finite_add a b hea heb ha hb]
  by_cases hz : Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b = 0
  · have hs : (Wasm.IEEE32.sign a && Wasm.IEEE32.sign b) = false := by
      cases hsa : Wasm.IEEE32.sign a <;> cases hsb : Wasm.IEEE32.sign b <;> try rfl
      simp only [Wasm.IEEE32.scaledValue, hsa, hsb, ↓reduceIte] at hz
      have hp : (0 : Int) < (Wasm.IEEE32.scaledMagnitude a : Int) := by
        exact_mod_cast Nat.pos_of_ne_zero ha
      have hq : (0 : Int) ≤ (Wasm.IEEE32.scaledMagnitude b : Int) := by omega
      omega
    simp [roundedSigned, Wasm.IEEE32.add, Wasm.IEEE32.isNaN, Wasm.IEEE32.isInfinite,
      hea, heb, hz, hs]
  · simp [roundedSigned, Wasm.IEEE32.add, Wasm.IEEE32.isNaN, Wasm.IEEE32.isInfinite,
      hea, heb, hz]

#print axioms add_eq_talos_finite

end Project.ProofKit.F32Decoded
