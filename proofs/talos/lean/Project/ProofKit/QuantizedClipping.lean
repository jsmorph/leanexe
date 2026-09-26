import Project.ProofKit.QuantizedError
import Mathlib.Data.Nat.Bitwise

set_option exponentiation.threshold 512

namespace Project.ProofKit.QuantizedClipping
open Wasm.IEEE32

theorem sign_mask (word : UInt32) : word &&& 0x80000000 = signMask (sign word) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and]
  change word.toNat &&& 2 ^ 31 = (signMask (sign word)).toNat
  rw [Nat.and_two_pow]
  by_cases h : 2 ^ 31 ≤ word.toNat
  · have hBit := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h word.toNat_lt
    norm_num only [show (2 : Nat) ^ 31 = 2147483648 from rfl] at h
    simp [signMask, sign, h, hBit]
  · have hBit := Nat.testBit_lt_two_pow (Nat.lt_of_not_ge h)
    norm_num only [show (2 : Nat) ^ 31 = 2147483648 from rfl] at h
    simp [signMask, sign, h, hBit]

theorem clipped_value (word : UInt32) :
    CodeLib.IEEE32.value (0x42FE0000 ||| (word &&& 0x80000000)) =
      if sign word then -127 else 127 := by
  rw [sign_mask]
  cases hSign : sign word
  · change CodeLib.IEEE32.value (0x42FE0000 : UInt32) = 127
    norm_num [CodeLib.IEEE32.value, scaledValue, scaledMagnitude,
      sign, exponent, fraction, UInt32.toNat_ofNat]
  · change CodeLib.IEEE32.value (0xC2FE0000 : UInt32) = -127
    norm_num [CodeLib.IEEE32.value, scaledValue, scaledMagnitude,
      sign, exponent, fraction, UInt32.toNat_ofNat]

theorem scaled_lower (word : UInt32) (h : 0x42FE0000 < word.toNat % 2 ^ 31) :
    127 * 2 ^ 149 ≤ scaledMagnitude word := by
  have he : 133 ≤ exponent word := by unfold exponent; omega
  by_cases he133 : exponent word = 133
  · have hf : 8257536 ≤ fraction word := by
      unfold exponent at he133
      unfold fraction
      omega
    simp only [scaledMagnitude, he133, beq_iff_eq,
      show ¬(133 : Nat) = 0 by decide, ite_false]
    omega
  · have hPow : (2 : Nat) ^ 133 ≤ 2 ^ (exponent word - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    simp only [scaledMagnitude, beq_iff_eq,
      show ¬exponent word = 0 by omega, ite_false]
    calc
      127 * 2 ^ 149 ≤ 2 ^ 23 * 2 ^ 133 := by decide
      _ ≤ (2 ^ 23 + fraction word) * 2 ^ (exponent word - 1) :=
        Nat.mul_le_mul (by omega) hPow

noncomputable def magnitude (word : UInt32) : ℝ := (scaledMagnitude word : ℝ) / 2 ^ 149

theorem value_eq (word : UInt32) :
    CodeLib.IEEE32.value word = if sign word then -magnitude word else magnitude word := by
  unfold CodeLib.IEEE32.value scaledValue magnitude
  split <;> simp [neg_div]

theorem abs_value (word : UInt32) : |CodeLib.IEEE32.value word| = magnitude word := by
  rw [value_eq]
  have h : 0 ≤ magnitude word := by unfold magnitude; positivity
  split <;> simp [abs_of_nonneg h]

theorem error (word : UInt32) :
    |CodeLib.IEEE32.value (QuantizedValue.clamp127 word) - CodeLib.IEEE32.value word| =
      Max.max 0 (|CodeLib.IEEE32.value word| - 127) := by
  have hPositive : (0 : ℝ) < 2 ^ 149 := by positivity
  by_cases h : (word &&& 0x7FFFFFFF) > 0x42FE0000
  · have hNat : 0x42FE0000 < word.toNat % 2 ^ 31 := by
      simpa only [UInt32.lt_iff_toNat_lt, QuantizedValue.magnitude_mask, UInt32.toNat_ofNat, Nat.reduceMod] using h
    have hBound : (127 : ℝ) * 2 ^ 149 ≤ scaledMagnitude word := by
      exact_mod_cast scaled_lower word hNat
    have hMagnitude : (127 : ℝ) ≤ magnitude word :=
      (le_div_iff₀ hPositive).mpr hBound
    rw [QuantizedValue.clamp127, if_pos h, clipped_value, abs_value,
      max_eq_right (by linarith : 0 ≤ magnitude word - 127), value_eq]
    cases hSign : sign word <;> simp [hSign, abs_of_nonneg (by linarith : 0 ≤ magnitude word - 127),
      abs_of_nonpos (by linarith : 127 - magnitude word ≤ 0)]
    rw [abs_of_nonneg (by linarith)]
    ring
  · have hNat : word.toNat % 2 ^ 31 ≤ 0x42FE0000 := by
      have h' : ¬(0x42FE0000 : UInt32).toNat < (word &&& 0x7FFFFFFF).toNat := h
      rw [QuantizedValue.magnitude_mask] at h'
      exact Nat.le_of_not_gt h'
    have hBound : (scaledMagnitude word : ℝ) ≤ 127 * 2 ^ 149 := by
      exact_mod_cast (QuantizedValue.scaled_bound word hNat).2
    have hMagnitude : magnitude word ≤ 127 := (div_le_iff₀ hPositive).mpr hBound
    simp [QuantizedValue.clamp127, h, abs_value, max_eq_left (by linarith : magnitude word - 127 ≤ 0)]

#print axioms error
end Project.ProofKit.QuantizedClipping
