import Verified.Source
import LeanExe.ProofKit.F32Bits
import LeanExe.ProofKit.F32Convert
import LeanExe.ProofKit.F32TruncSat
import LeanExe.ProofKit.F64Convert

namespace Verified.Float32Facts

open Float.Model Float.Model.UnpackedFloat LeanExe.ProofKit

theorem toBits_toFloat32 (n : UInt64) :
    n.toFloat32.toBits = Wasm.IEEE32.convertI64U n := by
  change (Float32.Model.ofInt (n.toNat : Int)).toBits = _
  rw [F32Convert.ofInt_eq]
  rfl

theorem clamp_nat (q : Nat) :
    UInt64.ofNatClamp q =
      if (q : Int) ≤ 0 then 0
      else if (2 : Int) ^ 64 - 1 ≤ q then 0xFFFFFFFFFFFFFFFF
      else Wasm.IEEE32.intToUInt64 q :=
  F64Convert.clamp_nat q

theorem truncSat_eq (value : UInt32) :
    (Float32.Model.ofBits value).unpack.toUInt64 = Wasm.IEEE32.truncSatI64U value := by
  rw [F32Packing.unpack_ofBits]
  by_cases he : Wasm.IEEE32.exponent value = 255
  · by_cases hf : Wasm.IEEE32.fraction value = 0
    · have hn : Wasm.IEEE32.isNaN value = false := by simp [Wasm.IEEE32.isNaN, he, hf]
      have hfin : Wasm.IEEE32.isFinite value = false := by simp [Wasm.IEEE32.isFinite, he]
      cases hs : Wasm.IEEE32.sign value <;>
        simp only [F32Encoding.decode, F32Encoding.sourceSign, he, hf, hs, hn, hfin,
          Bool.false_eq_true, ↓reduceIte, UnpackedFloat.toUInt64, toInt,
          Wasm.IEEE32.truncSatI64U, Wasm.IEEE32.truncatedInt] <;> decide +kernel
    · have hn : Wasm.IEEE32.isNaN value = true := by simp [Wasm.IEEE32.isNaN, he, hf]
      simp only [F32Encoding.decode, he, hf, ↓reduceIte, UnpackedFloat.toUInt64, toInt,
        Wasm.IEEE32.truncSatI64U, hn]
      rfl
  · by_cases hz : Wasm.IEEE32.scaledMagnitude value = 0
    · rw [F32Nearest.zero_encoding value hz]
      cases Wasm.IEEE32.sign value <;> decide +kernel
    · have hn : Wasm.IEEE32.isNaN value = false := by simp [Wasm.IEEE32.isNaN, he]
      have hfin : Wasm.IEEE32.isFinite value = true := by simp [Wasm.IEEE32.isFinite, he]
      rw [F32Decoded.decode_finite value he hz]
      simp only [UnpackedFloat.toUInt64, toInt,
        F32TruncSat.roundToInt_scaled _ _ _ (F32Decoded.exponent_ge value),
        F32Decoded.scaled_mantissa]
      cases hs : Wasm.IEEE32.sign value <;>
        simp only [F32Encoding.sourceSign, hs, Sign.apply, Wasm.IEEE32.truncSatI64U,
          Wasm.IEEE32.truncatedInt, hn, hfin, Bool.false_eq_true, ↓reduceIte]
      · exact clamp_nat _
      · rw [if_pos (by omega)]
        simp only [Int.toNat_neg_natCast]
        rfl

theorem toUInt64_eq (x : Float32) : x.toUInt64 = Wasm.IEEE32.truncSatI64U x.toBits := by
  change x.toModel.unpack.toUInt64 = _
  rw [F32Bits.toModel_eq, truncSat_eq]

theorem signed32_toFloat (x : UInt64) :
    (Int32.ofUInt32 x.toUInt32).toFloat32.toBits = Wasm.IEEE32.convertI32S x.toUInt32 :=
  F32Convert.ofInt32Bits_eq x.toUInt32

theorem to_signed32 (x : Float32) :
    x.toInt32.toUInt32.toUInt64 = (Wasm.IEEE32.truncSatI32S x.toBits).toUInt64 := by
  rw [← F32TruncSat.toInt32Bits_eq, LeanExe.Float32.toInt32Bits, F32Bits.ofBits_toBits]

theorem add_negZero (x : UInt32) :
    Wasm.IEEE32.add x 0x80000000 =
      if Wasm.IEEE32.isNaN x then Wasm.IEEE32.canonicalNaN else x := by
  unfold Wasm.IEEE32.add
  by_cases hn : Wasm.IEEE32.isNaN x
  · simp [hn]
  have hz : Wasm.IEEE32.isNaN 0x80000000 = false := by decide
  have hzi : Wasm.IEEE32.isInfinite 0x80000000 = false := by decide
  have hzv : Wasm.IEEE32.scaledValue 0x80000000 = 0 := by decide
  have hzs : Wasm.IEEE32.sign 0x80000000 = true := by decide
  simp only [hn, hz, Bool.or_false, Bool.false_eq_true, ite_false, hzi, hzv, Int.add_zero,
    hzs, Bool.and_true]
  by_cases hi : Wasm.IEEE32.isInfinite x
  · simp [hi]
  simp only [hi, Bool.false_eq_true, ite_false]
  have he : Wasm.IEEE32.exponent x ≠ 255 := by
    intro he
    simp only [Wasm.IEEE32.isNaN, Wasm.IEEE32.isInfinite, he] at hn hi
    simp_all
  by_cases hm : Wasm.IEEE32.scaledMagnitude x = 0
  · have hx := F32Nearest.zero_encoding x hm
    have hv : Wasm.IEEE32.scaledValue x = 0 := by simp [Wasm.IEEE32.scaledValue, hm]
    simp only [hv, beq_self_eq_true, ite_true]
    conv => rhs; rw [hx]
    cases Wasm.IEEE32.sign x <;> rfl
  · have hm' : (Wasm.IEEE32.scaledMagnitude x : Int) ≠ 0 := by exact_mod_cast hm
    have hv : Wasm.IEEE32.scaledValue x ≠ 0 := by
      simp only [Wasm.IEEE32.scaledValue]
      split <;> omega
    simp only [hv, beq_iff_eq, ite_false]
    have hneg : decide (Wasm.IEEE32.scaledValue x < 0) = Wasm.IEEE32.sign x := by
      simp only [Wasm.IEEE32.scaledValue]
      split <;> simp_all; omega
    have habs : (Wasm.IEEE32.scaledValue x).natAbs = Wasm.IEEE32.scaledMagnitude x := by
      simp only [Wasm.IEEE32.scaledValue]
      split <;> simp
    rw [hneg, habs]
    exact F32Decoded.roundScaled_value x he hm

#print axioms toBits_toFloat32
#print axioms toUInt64_eq
#print axioms signed32_toFloat
#print axioms to_signed32
#print axioms add_negZero

end Verified.Float32Facts
