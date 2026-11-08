import LeanExe.ProofKit.Signed64Float

/-!
Lean's conversions between `Int64` and the floats are WebAssembly's signed conversions as Talos
defines them: `Int64.toFloat` is `f64.convert_i64_s`, `Int64.toFloat32` is `f32.convert_i64_s`,
`Float.toInt64` is `i64.trunc_sat_f64_s`, and `Float32.toInt64` is `i64.trunc_sat_f32_s`.  The
verified compiler executes none of these instructions, since the reflector writes the conversions
with the word forms of `Signed64Float`, and the equations give specifications of the conversions
that do not mention Lean's model.  `toInt64_bits` and `toInt64_bits32` follow
`F64Convert.truncSat_eq` and `F32TruncSat.toInt32Bits_eq` through the decoded float.
-/

namespace LeanExe.ProofKit.Signed64Wasm

open Float.Model Float.Model.UnpackedFloat FloatCommon

theorem signedI64Value_eq (a : Int64) : Wasm.IEEE64.signedI64Value a.toUInt64 = a.toInt := by
  rw [Signed64.toInt_cond]
  simp only [Wasm.IEEE64.signedI64Value, Wasm.IEEE64.sign, decide_eq_true_eq]
  split <;> split <;> omega

theorem signedI64Value32_eq (a : Int64) : Wasm.IEEE32.signedI64Value a.toUInt64 = a.toInt := by
  rw [Signed64.toInt_cond]
  simp only [Wasm.IEEE32.signedI64Value]
  split <;> split <;> omega

theorem toBits_toFloat (a : Int64) : a.toFloat.toBits = Wasm.IEEE64.convertI64S a.toUInt64 := by
  unfold Wasm.IEEE64.convertI64S
  rw [Signed64.toBits_int64ToFloat, signedI64Value_eq]

theorem toBits_toFloat32 (a : Int64) :
    a.toFloat32.toBits = Wasm.IEEE32.convertI64S a.toUInt64 := by
  unfold Wasm.IEEE32.convertI64S
  rw [Signed64.toBits_int64ToFloat32, signedI64Value32_eq]

theorem int_word (value : Int) (lower : -(2 ^ 63) ≤ value) (upper : value < 2 ^ 63) :
    (Int64.ofInt value).toUInt64 = Wasm.IEEE64.intToUInt64 value := by
  apply UInt64.toNat.inj
  change (BitVec.ofInt 64 value).toNat = _
  simp only [BitVec.toNat_ofInt, Wasm.IEEE64.intToUInt64, UInt64.toNat_ofNat']
  by_cases hn : value < 0
  · have ha : (value.natAbs : Int) = -value := Int.ofNat_natAbs_of_nonpos (by omega)
    simp only [hn, ite_true]
    omega
  · have ha : (value.natAbs : Int) = value := Int.natAbs_of_nonneg (by omega)
    simp only [hn, ite_false]
    omega

/-- Lean's clamp of an integer into `Int64`, on words, in the form of `truncSatI64S`. -/
theorem clamp_word (value : Int) :
    (Int64.ofIntClamp value).toUInt64 =
      if value ≤ -(2 ^ 63) then 0x8000000000000000
      else if 2 ^ 63 - 1 ≤ value then 0x7FFFFFFFFFFFFFFF else Wasm.IEEE64.intToUInt64 value := by
  have hmin : Int64.minValue.toInt = -9223372036854775808 := by decide
  have hmax : Int64.maxValue.toInt = 9223372036854775807 := by decide
  by_cases hl : value ≤ -(2 ^ 63)
  · by_cases he : value = -(2 ^ 63)
    · subst value
      decide +kernel
    · have hn : ¬Int64.minValue.toInt ≤ value := by omega
      simp only [Int64.ofIntClamp, hn, hl, ↓reduceDIte, ↓reduceIte]
      rfl
  · by_cases hu : 2 ^ 63 - 1 ≤ value
    · by_cases he : value = 2 ^ 63 - 1
      · subst value
        decide +kernel
      · have hlo : Int64.minValue.toInt ≤ value := by omega
        have hhi : ¬value ≤ Int64.maxValue.toInt := by omega
        simp only [Int64.ofIntClamp, hlo, hhi, hl, hu, ↓reduceDIte, ↓reduceIte]
        rfl
    · have hlo : Int64.minValue.toInt ≤ value := by omega
      have hhi : value ≤ Int64.maxValue.toInt := by omega
      simp only [Int64.ofIntClamp, hlo, hhi, hl, hu, ↓reduceDIte, ↓reduceIte, Int64.ofIntLE]
      exact int_word value (by omega) (by omega)

theorem toInt64_bits (value : UInt64) :
    (Int64.ofIntClamp ((Float.Model.ofBits value).unpack.toInt Int64.minValue.toInt
      Int64.maxValue.toInt)).toUInt64 = Wasm.IEEE64.truncSatI64S value := by
  rw [F64Packing.unpack_ofBits]
  by_cases he : Wasm.IEEE64.exponent value = 2047
  · by_cases hf : Wasm.IEEE64.fraction value = 0
    · have hn : Wasm.IEEE64.isNaN value = false := by simp [Wasm.IEEE64.isNaN, he, hf]
      have hfin : Wasm.IEEE64.isFinite value = false := by simp [Wasm.IEEE64.isFinite, he]
      cases hs : Wasm.IEEE64.sign value <;>
        simp only [F64Encoding.decode, F64Encoding.sourceSign, he, hf, hs, hn, hfin,
          Bool.false_eq_true, ↓reduceIte, toInt, Wasm.IEEE64.truncSatI64S,
          Wasm.IEEE64.truncatedInt] <;> decide +kernel
    · have hn : Wasm.IEEE64.isNaN value = true := by simp [Wasm.IEEE64.isNaN, he, hf]
      simp only [F64Encoding.decode, he, hf, ↓reduceIte, toInt, Wasm.IEEE64.truncSatI64S, hn]
      decide +kernel
  · by_cases hz : Wasm.IEEE64.scaledMagnitude value = 0
    · rw [F64Convert.zero_encoding value hz]
      cases Wasm.IEEE64.sign value <;> decide +kernel
    · have hn : Wasm.IEEE64.isNaN value = false := by simp [Wasm.IEEE64.isNaN, he]
      have hfin : Wasm.IEEE64.isFinite value = true := by simp [Wasm.IEEE64.isFinite, he]
      rw [F64Decoded.decode_finite value he hz]
      simp only [toInt, F64Convert.roundToInt_scaled _ _ _ (F64Decoded.exponent_ge value),
        F64Decoded.scaled_mantissa]
      rw [clamp_word]
      cases hs : Wasm.IEEE64.sign value <;>
        simp only [F64Encoding.sourceSign, hs, Sign.apply, Wasm.IEEE64.truncSatI64S,
          Wasm.IEEE64.truncatedInt, hn, hfin, Bool.false_eq_true, ↓reduceIte]

theorem intToUInt64_eq (value : Int) :
    Wasm.IEEE32.intToUInt64 value = Wasm.IEEE64.intToUInt64 value := rfl

theorem toInt64_bits32 (value : UInt32) :
    (Int64.ofIntClamp ((Float32.Model.ofBits value).unpack.toInt Int64.minValue.toInt
      Int64.maxValue.toInt)).toUInt64 = Wasm.IEEE32.truncSatI64S value := by
  rw [F32Packing.unpack_ofBits]
  by_cases he : Wasm.IEEE32.exponent value = 255
  · by_cases hf : Wasm.IEEE32.fraction value = 0
    · have hn : Wasm.IEEE32.isNaN value = false := by simp [Wasm.IEEE32.isNaN, he, hf]
      have hfin : Wasm.IEEE32.isFinite value = false := by simp [Wasm.IEEE32.isFinite, he]
      cases hs : Wasm.IEEE32.sign value <;>
        simp only [F32Encoding.decode, F32Encoding.sourceSign, he, hf, hs, hn, hfin,
          Bool.false_eq_true, ↓reduceIte, toInt, Wasm.IEEE32.truncSatI64S,
          Wasm.IEEE32.truncatedInt] <;> decide +kernel
    · have hn : Wasm.IEEE32.isNaN value = true := by simp [Wasm.IEEE32.isNaN, he, hf]
      simp only [F32Encoding.decode, he, hf, ↓reduceIte, toInt, Wasm.IEEE32.truncSatI64S, hn]
      decide +kernel
  · by_cases hz : Wasm.IEEE32.scaledMagnitude value = 0
    · rw [F32Nearest.zero_encoding value hz]
      cases Wasm.IEEE32.sign value <;> decide +kernel
    · have hn : Wasm.IEEE32.isNaN value = false := by simp [Wasm.IEEE32.isNaN, he]
      have hfin : Wasm.IEEE32.isFinite value = true := by simp [Wasm.IEEE32.isFinite, he]
      rw [F32Decoded.decode_finite value he hz]
      simp only [toInt, F32TruncSat.roundToInt_scaled _ _ _ (F32Decoded.exponent_ge value),
        F32Decoded.scaled_mantissa]
      rw [clamp_word]
      cases hs : Wasm.IEEE32.sign value <;>
        simp only [F32Encoding.sourceSign, hs, Sign.apply, Wasm.IEEE32.truncSatI64S,
          Wasm.IEEE32.truncatedInt, hn, hfin, Bool.false_eq_true, ↓reduceIte, intToUInt64_eq]

theorem toInt64_eq (x : Float) : x.toInt64.toUInt64 = Wasm.IEEE64.truncSatI64S x.toBits := by
  change (Int64.ofIntClamp (x.toModel.unpack.toInt Int64.minValue.toInt
    Int64.maxValue.toInt)).toUInt64 = _
  rw [F64Bits.toModel_eq, toInt64_bits]

theorem toInt64_eq32 (x : Float32) :
    x.toInt64.toUInt64 = Wasm.IEEE32.truncSatI64S x.toBits := by
  change (Int64.ofIntClamp (x.toModel.unpack.toInt Int64.minValue.toInt
    Int64.maxValue.toInt)).toUInt64 = _
  rw [F32Bits.toModel_eq, toInt64_bits32]

#print axioms toBits_toFloat
#print axioms toBits_toFloat32
#print axioms toInt64_eq
#print axioms toInt64_eq32

end LeanExe.ProofKit.Signed64Wasm
