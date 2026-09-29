import Project.ProofKit.F32Decoded
import Project.ProofKit.F32Nearest

namespace Project.ProofKit.F32TruncSat
open Float.Model Float.Model.UnpackedFloat

theorem roundToInt_eq (s : Sign) (m : Nat) (e : Int) :
    roundToInt s m e = s.apply ((m * 2 ^ e.toNat / 2 ^ (-e).toNat : Nat) : Int) := by
  simp only [roundToInt, decreaseExponent, sub_zero, shiftToExponent]
  rw [F32Rounding.shift_mantissa]
  have he : (0 - (e - e.toNat)).toNat = (-e).toNat := by omega
  rw [he, Nat.shiftLeft_eq]
  rfl

theorem scaled_truncate (m : Nat) (e : Int) (he : -149 ≤ e) :
    m * 2 ^ e.toNat / 2 ^ (-e).toNat = m * 2 ^ (e + 149).toNat / 2 ^ 149 := by
  by_cases hp : 0 ≤ e
  · have hn : (-e).toNat = 0 := by omega
    have ha : (e + 149).toNat = e.toNat + 149 := by omega
    simp [hn, ha, pow_add, ← Nat.mul_assoc]
  · have hn : e.toNat = 0 := by omega
    have ha : 149 = (e + 149).toNat + (-e).toNat := by omega
    rw [hn, pow_zero, Nat.mul_one, ha, pow_add, ← Nat.div_div_eq_div_mul]
    simp

theorem roundToInt_scaled (s : Sign) (m : Nat) (e : Int) (he : -149 ≤ e) :
    roundToInt s m e = s.apply ((m * 2 ^ (e + 149).toNat / 2 ^ 149 : Nat) : Int) := by
  rw [roundToInt_eq, scaled_truncate m e he]

theorem int_word (value : Int) (lower : -(2 ^ 31) ≤ value) (upper : value < 2 ^ 31) :
    (Int32.ofInt value).toUInt32 = Wasm.IEEE32.intToUInt32 value := by
  apply UInt32.toNat.inj
  change (BitVec.ofInt 32 value).toNat = _
  simp only [BitVec.toNat_ofInt, Wasm.IEEE32.intToUInt32, UInt32.toNat_ofNat']
  by_cases hn : value < 0
  · have ha : (value.natAbs : Int) = -value := Int.ofNat_natAbs_of_nonpos (by omega)
    simp only [hn, ite_true]
    omega
  · have ha : (value.natAbs : Int) = value := Int.natAbs_of_nonneg (by omega)
    simp only [hn, ite_false]
    omega

theorem clamp_word (value : Int) :
    (Int32.ofIntClamp value).toUInt32 =
      if value ≤ -(2 ^ 31) then 0x80000000
      else if 2 ^ 31 - 1 ≤ value then 0x7FFFFFFF else Wasm.IEEE32.intToUInt32 value := by
  have hmin : Int32.minValue.toInt = -2147483648 := by decide
  have hmax : Int32.maxValue.toInt = 2147483647 := by decide
  by_cases hl : value ≤ -(2 ^ 31)
  · by_cases he : value = -(2 ^ 31)
    · subst value
      decide
    · have hn : ¬Int32.minValue.toInt ≤ value := by omega
      simp only [Int32.ofIntClamp, hn, hl, ↓reduceDIte, ↓reduceIte]
      rfl
  · by_cases hu : 2 ^ 31 - 1 ≤ value
    · by_cases he : value = 2 ^ 31 - 1
      · subst value
        decide
      · have hlo : Int32.minValue.toInt ≤ value := by omega
        have hhi : ¬value ≤ Int32.maxValue.toInt := by omega
        simp only [Int32.ofIntClamp, hlo, hhi, hl, hu, ↓reduceDIte, ↓reduceIte]
        rfl
    · have hlo : Int32.minValue.toInt ≤ value := by omega
      have hhi : value ≤ Int32.maxValue.toInt := by omega
      simp only [Int32.ofIntClamp, hlo, hhi, hl, hu, ↓reduceDIte, ↓reduceIte, Int32.ofIntLE]
      exact int_word value (by omega) (by omega)

theorem toInt32Bits_eq (value : UInt32) :
    LeanExe.Float32.toInt32Bits value = Wasm.IEEE32.truncSatI32S value := by
  by_cases he : Wasm.IEEE32.exponent value = 255
  · change (Int32.ofIntClamp ((Float32.Model.ofBits value).unpack.toInt
      Int32.minValue.toInt Int32.maxValue.toInt)).toUInt32 = _
    rw [F32Packing.unpack_ofBits]
    by_cases hf : Wasm.IEEE32.fraction value = 0
    · cases hs : Wasm.IEEE32.sign value <;>
        simp [F32Encoding.decode, F32Encoding.sourceSign, he, hf, hs, toInt,
          Wasm.IEEE32.truncSatI32S, Wasm.IEEE32.truncatedInt, Wasm.IEEE32.isNaN, Wasm.IEEE32.isFinite] <;> decide
    · simp [F32Encoding.decode, he, hf, toInt,
        Wasm.IEEE32.truncSatI32S, Wasm.IEEE32.isNaN]
      decide
  · by_cases hz : Wasm.IEEE32.scaledMagnitude value = 0
    · rw [F32Nearest.zero_encoding value hz]
      cases Wasm.IEEE32.sign value <;> decide
    · change (Int32.ofIntClamp ((Float32.Model.ofBits value).unpack.toInt
        Int32.minValue.toInt Int32.maxValue.toInt)).toUInt32 = _
      rw [F32Packing.unpack_ofBits, F32Decoded.decode_finite value he hz]
      simp only [toInt, roundToInt_scaled _ _ _ (F32Decoded.exponent_ge value), F32Decoded.scaled_mantissa]
      rw [clamp_word]
      cases hs : Wasm.IEEE32.sign value <;>
        simp [F32Encoding.sourceSign, Sign.apply, hs, Wasm.IEEE32.truncSatI32S,
          Wasm.IEEE32.truncatedInt, Wasm.IEEE32.isNaN, Wasm.IEEE32.isFinite, he]

#print axioms roundToInt_scaled
#print axioms toInt32Bits_eq

end Project.ProofKit.F32TruncSat
