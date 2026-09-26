import Project.ProofKit.F32UniformRangeCertificate
import Project.ProofKit.F32IntegerMagnitude
import LeanExe.Models.Gpt2.Quantized.Kernel

namespace Project.ProofKit.QuantizedUniformRange
open LeanExe.Models.Gpt2.Quantized CodeLib.IEEE32

theorem rescale_ranges (accumulator inputScale weightScale : UInt32)
    (inputMagnitude weightMagnitude scaleBound outputBound : Nat)
    (h : F32UniformRange.rescaleFits inputMagnitude weightMagnitude scaleBound outputBound = true)
    (ha : (LeanExe.Signed32.decode accumulator).natAbs ≤ 1032256)
    (hi : CodeLib.IEEE32.Finite inputScale) (hw : CodeLib.IEEE32.Finite weightScale)
    (hI : Wasm.IEEE32.scaledMagnitude inputScale ≤ inputMagnitude)
    (hW : Wasm.IEEE32.scaledMagnitude weightScale ≤ weightMagnitude) :
    Wasm.IEEE32.scaledMagnitude inputScale * Wasm.IEEE32.scaledMagnitude weightScale < 2 ^ scaleBound ∧
    Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.ofInt32Bits accumulator) *
      Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.mulBits inputScale weightScale) < 2 ^ outputBound ∧
    CodeLib.IEEE32.Finite (rescale accumulator inputScale weightScale) ∧
      (Wasm.IEEE32.scaledValue (rescale accumulator inputScale weightScale)).natAbs ≤
        F32UniformRange.productMagnitude outputBound := by
  simp only [F32UniformRange.rescaleFits, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  have hScale := (Nat.mul_le_mul hI hW).trans_lt h.2.2.2.2.1
  have hs := F32UniformRange.product_magnitude inputScale weightScale scaleBound h.1 h.2.1 hi hw hScale
  have ha' : (LeanExe.Signed32.decode accumulator).natAbs < 2 ^ 24 := by omega
  have hc := F32IntegerExact.conversion_exact accumulator ha'
  have hmag := F32IntegerExact.conversion_magnitude accumulator ha'
  have hOutput : Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.ofInt32Bits accumulator) *
      Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.mulBits inputScale weightScale) < 2 ^ outputBound := by
    rw [hmag]
    have hm : Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.mulBits inputScale weightScale) ≤
        F32UniformRange.productMagnitude scaleBound := by simpa only [natAbs_scaledValue] using hs.2
    exact (Nat.mul_le_mul (Nat.mul_le_mul_right _ ha) hm).trans_lt h.2.2.2.2.2
  exact ⟨hScale, hOutput, F32UniformRange.product_magnitude _ _ outputBound h.2.2.1 h.2.2.2.1 hc.1 hs.1 hOutput⟩

#print axioms rescale_ranges
end Project.ProofKit.QuantizedUniformRange
