import Project.ProofKit.QuantizedExport

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

#print axioms reconstruction
#print axioms captured_scale_bound
end Project.ProofKit.QuantizedRangeCertificate
