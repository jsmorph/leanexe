import LeanExe.Models.Gpt2.Quantized.Kernel
import Project.ProofKit.F32TruncSat
import Project.ProofKit.PackedByteSource

namespace Project.ProofKit.QuantizedValue
open Wasm.IEEE32

theorem magnitude_mask (value : UInt32) :
    (value &&& 0x7FFFFFFF).toNat = value.toNat % 2 ^ 31 := by
  rw [UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod value.toNat 31

theorem scaled_bound (value : UInt32) (h : value.toNat % 2 ^ 31 ≤ 0x42FE0000) :
    exponent value ≠ 255 ∧ scaledMagnitude value ≤ 127 * 2 ^ 149 := by
  have he : exponent value ≤ 133 := by unfold exponent; omega
  refine ⟨by omega, ?_⟩
  have hf := CodeLib.IEEE32.fraction_lt value
  by_cases he0 : exponent value = 0
  · simp only [scaledMagnitude, beq_iff_eq, he0, ↓reduceIte]
    omega
  · by_cases he133 : exponent value = 133
    · have hf' : fraction value ≤ 8257536 := by
        unfold exponent at he133
        unfold fraction
        omega
      simp only [scaledMagnitude, beq_iff_eq, he133,
        show ¬(133 : Nat) = 0 by decide, ite_false]
      omega
    · have hpow : 2 ^ (exponent value - 1) ≤ (2 : Nat) ^ 131 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      simp only [scaledMagnitude, beq_iff_eq, he0, ↓reduceIte]
      calc
        (2 ^ 23 + fraction value) * 2 ^ (exponent value - 1) ≤ 2 ^ 24 * 2 ^ 131 :=
          Nat.mul_le_mul (by omega) hpow
        _ ≤ 127 * 2 ^ 149 := by decide

theorem roundShift_bound (m : Nat) (h : m ≤ 127 * 2 ^ 149) :
    roundShift m 149 ≤ 127 := by
  have hb := CodeLib.IEEE32.roundShift_bounds m 149
  by_cases he : m = 127 * 2 ^ 149
  · subst m
    decide
  · omega

theorem rounded_byte (n : Fin 128) (negative : Bool) :
    (Wasm.IEEE32.truncSatI32S (roundScaledMagnitude negative (n.val * 2 ^ 149))).toUInt8 =
      UInt8.ofNat (if negative then 256 - n.val else n.val) := by
  revert n negative
  decide +kernel

def clamp127 (value : UInt32) : UInt32 :=
  if (value &&& 0x7FFFFFFF) > 0x42FE0000 then
    0x42FE0000 ||| (value &&& 0x80000000)
  else value

theorem clipped_mask (value : UInt32) :
    ((0x42FE0000 ||| (value &&& 0x80000000)) &&& 0x7FFFFFFF) = 0x42FE0000 := by
  apply UInt32.toBitVec_inj.mp
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  interval_cases bit <;> simp

theorem clamp127_bound (value : UInt32) :
    (clamp127 value).toNat % 2 ^ 31 ≤ 0x42FE0000 := by
  rw [← magnitude_mask]
  unfold clamp127
  split
  · rw [clipped_mask]
    decide
  · rename_i h
    have hn : ¬(0x42FE0000 : UInt32).toNat < (value &&& 0x7FFFFFFF).toNat := h
    exact Nat.le_of_not_gt hn

theorem quantizeValue_valid (value scale : UInt32) :
    LeanExe.Models.Gpt2.Quantized.quantizeValue value scale ≠ 128 := by
  let clamped := clamp127 (LeanExe.Float32.divBits value scale)
  have hb := scaled_bound clamped (clamp127_bound _)
  have hn := roundShift_bound (scaledMagnitude clamped) hb.2
  change (LeanExe.Float32.toInt32Bits (LeanExe.Float32.nearestBits clamped)).toUInt8 ≠ 128
  rw [F32Nearest.nearestBits_finite clamped hb.1, F32TruncSat.toInt32Bits_eq,
    rounded_byte ⟨roundShift (scaledMagnitude clamped) 149, by omega⟩]
  intro h
  have hh := congrArg UInt8.toNat h
  have h128 : (128 : UInt8).toNat = 128 := rfl
  rw [h128] at hh
  cases hs : sign clamped <;> norm_num [hs, UInt8.toNat_ofNat'] at hh <;> omega

theorem quantizeValue_range (value scale : UInt32) :
    |LeanExe.Signed32.decode (LeanExe.Signed32.extend8Bits
      (LeanExe.Models.Gpt2.Quantized.quantizeValue value scale).toUInt32)| ≤ 127 :=
  QuantizedInt32.byte_range _ (quantizeValue_valid value scale)

theorem quantizeRows_valid (input : ByteArray) (width rows index : Nat)
    (hi : index < rows * width) :
    (LeanExe.Models.Gpt2.Quantized.quantizeRows input width rows).values[index]! ≠ 128 := by
  unfold LeanExe.Models.Gpt2.Quantized.quantizeRows
  rw [PackedByteSource.generate_byte _ _ _ hi]
  exact quantizeValue_valid _ _

#print axioms quantizeValue_valid
#print axioms quantizeRows_valid

end Project.ProofKit.QuantizedValue
