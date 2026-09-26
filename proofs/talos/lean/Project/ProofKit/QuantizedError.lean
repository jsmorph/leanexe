import Project.ProofKit.QuantizedValue
import Project.ProofKit.QuantizationError
import CodeLib.IEEE32.Roundoff

set_option exponentiation.threshold 512

namespace Project.ProofKit.QuantizedError
open Wasm.IEEE32 LeanExe.Models.Gpt2.Quantized

abbrev coefficient (input scale : UInt32) : Int :=
  LeanExe.Signed32.decode (LeanExe.Signed32.extend8Bits (quantizeValue input scale).toUInt32)

theorem decoded_byte (n : Fin 128) (negative : Bool) :
    LeanExe.Signed32.decode (LeanExe.Signed32.extend8Bits
      (UInt8.ofNat (if negative then 256 - n.val else n.val)).toUInt32) =
        if negative then -(n.val : Int) else n.val := by
  revert n negative
  decide +kernel

theorem coefficient_exact (input scale : UInt32) :
    let clipped := QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale)
    coefficient input scale = if sign clipped then
      -(roundShift (scaledMagnitude clipped) 149 : Int)
    else (roundShift (scaledMagnitude clipped) 149 : Int) := by
  let clipped := QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale)
  have hBound := QuantizedValue.scaled_bound clipped (QuantizedValue.clamp127_bound _)
  have hRound := QuantizedValue.roundShift_bound (scaledMagnitude clipped) hBound.2
  change LeanExe.Signed32.decode (LeanExe.Signed32.extend8Bits
    (LeanExe.Float32.toInt32Bits (LeanExe.Float32.nearestBits clipped)).toUInt8.toUInt32) = _
  rw [F32Nearest.nearestBits_finite clipped hBound.1, F32TruncSat.toInt32Bits_eq,
    QuantizedValue.rounded_byte ⟨roundShift (scaledMagnitude clipped) 149, by omega⟩,
    decoded_byte]

theorem nearest_scaled_error (input scale : UInt32) :
    let clipped := QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale)
    |coefficient input scale * (2 ^ 149 : Int) - scaledValue clipped| ≤ (2 ^ 148 : Int) := by
  let clipped := QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale)
  have h := CodeLib.IEEE32.abs_int_sub_le_of_error_cases _ _ _
    (CodeLib.IEEE32.roundShift_error_cases (scaledMagnitude clipped) 149 (by decide))
  have hError : |(roundShift (scaledMagnitude clipped) 149 : Int) * 2 ^ 149 -
      (scaledMagnitude clipped : Int)| ≤ (2 ^ 148 : Int) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    norm_num at h ⊢
    exact h
  rw [coefficient_exact]
  change |(if sign clipped then -(roundShift (scaledMagnitude clipped) 149 : Int)
    else (roundShift (scaledMagnitude clipped) 149 : Int)) * 2 ^ 149 - scaledValue clipped| ≤ _
  cases hSign : sign clipped
  · simpa only [scaledValue, hSign, Bool.false_eq_true, ite_false] using hError
  · simpa only [scaledValue, hSign, ite_true, neg_mul, neg_sub_neg, abs_sub_comm] using hError

theorem nearest_error (input scale : UInt32) :
    |(coefficient input scale : ℝ) - CodeLib.IEEE32.value
      (QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale))| ≤ 1 / 2 := by
  have h := nearest_scaled_error input scale
  have hReal : |(coefficient input scale : ℝ) * (2 : ℝ) ^ 149 -
      (scaledValue (QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale)) : ℝ)| ≤
        (2 : ℝ) ^ 148 := by
    exact_mod_cast h
  rw [CodeLib.IEEE32.value]
  have hEq : (coefficient input scale : ℝ) -
      (scaledValue (QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale)) : ℝ) / 2 ^ 149 =
      ((coefficient input scale : ℝ) * 2 ^ 149 -
        (scaledValue (QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale)) : ℝ)) / 2 ^ 149 := by
    field_simp
  rw [hEq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 149)).mpr
  norm_num at hReal ⊢
  exact hReal

theorem reconstruction_error (input scale : UInt32) (quotientError clipError : ℝ)
    (hScale : 0 < CodeLib.IEEE32.value scale)
    (hQuotient : |CodeLib.IEEE32.value (LeanExe.Float32.divBits input scale) -
      CodeLib.IEEE32.value input / CodeLib.IEEE32.value scale| ≤ quotientError)
    (hClip : |CodeLib.IEEE32.value (QuantizedValue.clamp127 (LeanExe.Float32.divBits input scale)) -
      CodeLib.IEEE32.value (LeanExe.Float32.divBits input scale)| ≤ clipError) :
    |CodeLib.IEEE32.value scale * (coefficient input scale : ℝ) - CodeLib.IEEE32.value input| ≤
      CodeLib.IEEE32.value scale * (1 / 2 + clipError + quotientError) :=
  QuantizationError.reconstruction_error _ _ _ _ _ _ _ _ hScale hQuotient hClip
    (nearest_error input scale)

#print axioms coefficient_exact
#print axioms nearest_error
#print axioms reconstruction_error
end Project.ProofKit.QuantizedError
