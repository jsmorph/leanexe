import Project.ProofKit.QuantizedExport
import Project.ProofKit.F32Absolute

set_option exponentiation.threshold 512

namespace Project.ProofKit.QuantizedRangeCertificate
open CodeLib.IEEE32 LeanExe.Models.Gpt2

theorem reconstruction (source coefficients : ByteArray) (offset width : Nat) (scale : UInt32)
    (h : QuantizedExport.checkRow source coefficients offset width scale = true)
    (i : Nat) (hi : i < width)
    (hq : |value (LeanExe.Float32.divBits (word source i) scale)| ≤ 127 + 1 / 131072) :
    |value scale * (LeanExe.Signed32.decode
      (LeanExe.Signed32.extend8Bits coefficients[offset + i]!.toUInt32) : ℝ) - value (word source i)| ≤
        value scale * (1 / 2 + 1 / 65536) := by
  have hr := QuantizedExport.reconstruction source coefficients offset width scale h i hi
  have hf := QuantizedExport.checked_row source coefficients offset width scale h
  have hs : 0 ≤ value scale := by
    unfold value
    exact div_nonneg (by exact_mod_cast hf.2.2.2.2.1.le) (by positivity)
  have hclip : max 0 (|value (LeanExe.Float32.divBits (word source i) scale)| - 127) ≤ 1 / 131072 := by
    exact max_le (by norm_num) (by linarith)
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ hs
  norm_num [F32DivisionBounds.epsilon]
  linarith

theorem captured_scale_bound :
    value (1074517830 : UInt32) * (1 / 2 + 1 / 65536) < 1093 / 1000 := by
  norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
    Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]

theorem reconstruction_uniform (source coefficients : ByteArray) (offset width : Nat) (scale : UInt32)
    (h : QuantizedExport.checkRow source coefficients offset width scale = true)
    (i : Nat) (hi : i < width) :
    |value scale * (LeanExe.Signed32.decode
      (LeanExe.Signed32.extend8Bits coefficients[offset + i]!.toUInt32) : ℝ) - value (word source i)| ≤
        value scale * (3 / 2 + 1 / 65536) := by
  have hf := QuantizedExport.checked_row source coefficients offset width scale h
  have hs : 0 < value scale := by
    unfold value
    exact div_pos (by exact_mod_cast hf.2.2.2.2.1) (by positivity)
  have hn : Wasm.IEEE32.scaledMagnitude scale ≠ 0 := by
    intro hz
    simp only [Wasm.IEEE32.scaledValue, hz, Int.natCast_zero, neg_zero, ite_self] at hf
    omega
  have hd := F32DivisionBounds.div_real_error (word source i) scale 156 (by decide) (by decide)
    (hf.2.2.2.2.2 i hi).1 hf.2.2.2.1 hn (hf.2.2.2.2.2 i hi).2.2.2
  rw [← F32Div.div_eq] at hd
  have ratio : |value (word source i) / value scale| ≤ 128 := by
    rw [abs_div, F32Order.abs_value_scaledMagnitude, F32Order.abs_value_scaledMagnitude, div_div_div_cancel_right₀ (by positivity)]
    apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
    have hb : (Wasm.IEEE32.scaledMagnitude (word source i) : ℝ) * 2 ^ 149 ≤
        (Wasm.IEEE32.scaledMagnitude scale : ℝ) * 2 ^ 156 := by
      exact_mod_cast (hf.2.2.2.2.2 i hi).2.2.2
    norm_num at hb
    nlinarith
  have hq := (abs_add_le (value (LeanExe.Float32.divBits (word source i) scale) - value (word source i) / value scale)
    (value (word source i) / value scale)).trans (add_le_add hd.2 ratio)
  rw [sub_add_cancel] at hq
  have hc : max 0 (|value (LeanExe.Float32.divBits (word source i) scale)| - 127) ≤
      1 + 1 / 131072 := by
    apply max_le (by norm_num)
    norm_num [F32DivisionBounds.epsilon] at hq
    linarith
  apply (QuantizedExport.reconstruction source coefficients offset width scale h i hi).trans
  apply mul_le_mul_of_nonneg_left _ hs.le
  norm_num [F32DivisionBounds.epsilon]
  linarith

#print axioms reconstruction
#print axioms captured_scale_bound
#print axioms reconstruction_uniform
end Project.ProofKit.QuantizedRangeCertificate
