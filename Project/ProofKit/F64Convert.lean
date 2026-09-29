import Project.ProofKit.F64Bits
import Project.ProofKit.F64Normalize
import Project.ProofKit.F32TruncSat

/-!
Lean's conversions between `UInt64` and `Float` agree with WebAssembly's
`f64.convert_i64_u` and `i64.trunc_sat_f64_u`.
-/

namespace Project.ProofKit.F64Convert
open Float.Model Float.Model.UnpackedFloat FloatCommon F64Encoding

theorem ofInt_eq (value : Int) :
    (Float.Model.ofInt value).toBits = Wasm.IEEE64.fromInt value := by
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.normalize Format.binary64 value 0 .positive)) = _
  rw [F64Normalize.pack_normalize value 0 .positive (by omega)]
  by_cases hz : value = 0
  · subst value
    decide +kernel
  · simp only [hz, ite_false, Wasm.IEEE64.fromInt]
    rfl

theorem toBits_toFloat (n : UInt64) : n.toFloat.toBits = Wasm.IEEE64.convertI64U n := by
  change (Float.Model.ofInt (n.toNat : Int)).toBits = _
  rw [ofInt_eq]
  rfl

theorem zero_encoding (value : UInt64) (hz : Wasm.IEEE64.scaledMagnitude value = 0) :
    value = Wasm.IEEE64.signMask (Wasm.IEEE64.sign value) := by
  have he : Wasm.IEEE64.exponent value = 0 := by
    by_contra he
    have hp : 0 < (2 ^ 52 + Wasm.IEEE64.fraction value) * 2 ^ (Wasm.IEEE64.exponent value - 1) :=
      Nat.mul_pos (by omega) (by positivity)
    simp [Wasm.IEEE64.scaledMagnitude, he] at hz
  have hf : Wasm.IEEE64.fraction value = 0 := by
    simpa [Wasm.IEEE64.scaledMagnitude, he] using hz
  calc
    value = Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign value)
        (Wasm.IEEE64.exponent value) (Wasm.IEEE64.fraction value) :=
      (F64Packing.encode_fields value).symm
    _ = Wasm.IEEE64.signMask (Wasm.IEEE64.sign value) := by
      rw [he, hf, ← F64Packing.signMask_eq_encode]

theorem scaled_truncate (m : Nat) (e : Int) (he : -1074 ≤ e) :
    m * 2 ^ e.toNat / 2 ^ (-e).toNat = m * 2 ^ (e + 1074).toNat / 2 ^ 1074 := by
  by_cases hp : 0 ≤ e
  · have hn : (-e).toNat = 0 := by omega
    have ha : (e + 1074).toNat = e.toNat + 1074 := by omega
    simp [hn, ha, pow_add, ← Nat.mul_assoc]
  · have hn : e.toNat = 0 := by omega
    have ha : 1074 = (e + 1074).toNat + (-e).toNat := by omega
    rw [hn, pow_zero, Nat.mul_one, ha, pow_add, ← Nat.div_div_eq_div_mul]
    simp

theorem roundToInt_scaled (s : Sign) (m : Nat) (e : Int) (he : -1074 ≤ e) :
    roundToInt s m e = s.apply ((m * 2 ^ (e + 1074).toNat / 2 ^ 1074 : Nat) : Int) := by
  rw [F32TruncSat.roundToInt_eq, scaled_truncate m e he]

theorem clamp_nat (q : Nat) :
    UInt64.ofNatClamp q =
      if (q : Int) ≤ 0 then 0
      else if (2 : Int) ^ 64 - 1 ≤ q then 0xFFFFFFFFFFFFFFFF
      else Wasm.IEEE64.intToUInt64 q := by
  have hs : UInt64.size = 18446744073709551616 := rfl
  unfold UInt64.ofNatClamp
  split_ifs with h1 h2 h3 h4 <;> apply UInt64.toNat.inj <;>
    simp only [UInt64.toNat_ofNatLT, Wasm.IEEE64.intToUInt64, Int.natAbs_natCast,
      show ¬(q : Int) < 0 by omega, ↓reduceIte, UInt64.toNat_ofNat', UInt64.toNat_zero,
      UInt64.reduceToNat] <;> first | rfl | omega

theorem truncSat_eq (value : UInt64) :
    (Float.Model.ofBits value).unpack.toUInt64 = Wasm.IEEE64.truncSatI64U value := by
  rw [F64Packing.unpack_ofBits]
  by_cases he : Wasm.IEEE64.exponent value = 2047
  · by_cases hf : Wasm.IEEE64.fraction value = 0
    · have hn : Wasm.IEEE64.isNaN value = false := by simp [Wasm.IEEE64.isNaN, he, hf]
      have hfin : Wasm.IEEE64.isFinite value = false := by simp [Wasm.IEEE64.isFinite, he]
      cases hs : Wasm.IEEE64.sign value <;>
        simp only [decode, sourceSign, he, hf, hs, hn, hfin, Bool.false_eq_true, ↓reduceIte,
          UnpackedFloat.toUInt64, toInt, Wasm.IEEE64.truncSatI64U, Wasm.IEEE64.truncatedInt] <;>
        decide +kernel
    · have hn : Wasm.IEEE64.isNaN value = true := by simp [Wasm.IEEE64.isNaN, he, hf]
      simp only [decode, he, hf, ↓reduceIte, UnpackedFloat.toUInt64, toInt,
        Wasm.IEEE64.truncSatI64U, hn]
      rfl
  · by_cases hz : Wasm.IEEE64.scaledMagnitude value = 0
    · rw [zero_encoding value hz]
      cases Wasm.IEEE64.sign value <;> decide +kernel
    · have hn : Wasm.IEEE64.isNaN value = false := by simp [Wasm.IEEE64.isNaN, he]
      have hfin : Wasm.IEEE64.isFinite value = true := by simp [Wasm.IEEE64.isFinite, he]
      rw [F64Decoded.decode_finite value he hz]
      simp only [UnpackedFloat.toUInt64, toInt,
        roundToInt_scaled _ _ _ (F64Decoded.exponent_ge value), F64Decoded.scaled_mantissa]
      cases hs : Wasm.IEEE64.sign value <;>
        simp only [sourceSign, hs, Sign.apply, Wasm.IEEE64.truncSatI64U,
          Wasm.IEEE64.truncatedInt, hn, hfin, Bool.false_eq_true, ↓reduceIte]
      · exact clamp_nat _
      · rw [if_pos (by omega)]
        simp only [Int.toNat_neg_natCast]
        rfl

theorem toUInt64_eq (x : Float) : x.toUInt64 = Wasm.IEEE64.truncSatI64U x.toBits := by
  change x.toModel.unpack.toUInt64 = _
  rw [F64Bits.toModel_eq, truncSat_eq]

#print axioms toBits_toFloat
#print axioms toUInt64_eq

end Project.ProofKit.F64Convert
