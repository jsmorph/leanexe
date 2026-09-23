import Project.ProofKit.QuantizedScalarError
import Project.ProofKit.F32Div
import LeanExe.Models.Gpt2.Quantized.Kernel

namespace Project.ProofKit.QuantizedExport
open CodeLib.IEEE32 LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

def roundedCoefficient (input scale : UInt32) : Int :=
  let clipped := QuantizedValue.clamp127 (Wasm.IEEE32.div input scale)
  if Wasm.IEEE32.sign clipped then
    -(Wasm.IEEE32.roundShift (Wasm.IEEE32.scaledMagnitude clipped) 149 : Int)
  else Wasm.IEEE32.roundShift (Wasm.IEEE32.scaledMagnitude clipped) 149

theorem roundedCoefficient_eq (input scale : UInt32) :
    roundedCoefficient input scale = QuantizedError.coefficient input scale := by
  rw [QuantizedError.coefficient_exact, F32Div.div_eq]
  rfl

def checkRow (source : ByteArray) (coefficients : ByteArray) (offset width : Nat)
    (scale : UInt32) : Bool :=
  source.size == width * 4 && offset + width ≤ coefficients.size &&
    scale == rowScale source 0 width && Wasm.IEEE32.isFinite scale &&
    decide (0 < Wasm.IEEE32.scaledValue scale) &&
    (List.range width).all (fun i =>
      Wasm.IEEE32.isFinite (word source i) && coefficients[offset + i]! != 128 &&
      decide (LeanExe.Signed32.decode (LeanExe.Signed32.extend8Bits coefficients[offset + i]!.toUInt32) =
        roundedCoefficient (word source i) scale) &&
      decide (Wasm.IEEE32.scaledMagnitude (word source i) * 2 ^ 149 ≤
        Wasm.IEEE32.scaledMagnitude scale * 2 ^ 156))

theorem checked_row (source coefficients : ByteArray) (offset width : Nat) (scale : UInt32)
    (h : checkRow source coefficients offset width scale = true) :
    source.size = width * 4 ∧ offset + width ≤ coefficients.size ∧
      scale = rowScale source 0 width ∧ Finite scale ∧ 0 < Wasm.IEEE32.scaledValue scale ∧
      ∀ i < width, Finite (word source i) ∧ coefficients[offset + i]! ≠ 128 ∧
        LeanExe.Signed32.decode (LeanExe.Signed32.extend8Bits coefficients[offset + i]!.toUInt32) =
          QuantizedError.coefficient (word source i) scale ∧
        Wasm.IEEE32.scaledMagnitude (word source i) * 2 ^ 149 ≤
          Wasm.IEEE32.scaledMagnitude scale * 2 ^ 156 := by
  simpa only [checkRow, CodeLib.IEEE32.Finite, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    List.all_eq_true, List.mem_range, and_assoc, roundedCoefficient_eq] using h

theorem reconstruction (source coefficients : ByteArray) (offset width : Nat) (scale : UInt32)
    (h : checkRow source coefficients offset width scale = true) (i : Nat) (hi : i < width) :
    |value scale * (LeanExe.Signed32.decode
          (LeanExe.Signed32.extend8Bits coefficients[offset + i]!.toUInt32) : ℝ) - value (word source i)| ≤
      value scale * (1 / 2 + max 0 (|value (LeanExe.Float32.divBits (word source i) scale)| - 127) +
        F32DivisionBounds.epsilon 156) := by
  obtain ⟨_, _, _, hScaleFinite, hScalePositive, hFields⟩ := checked_row source coefficients offset width scale h
  obtain ⟨hInput, _, hCoefficient, hQuotient⟩ := hFields i hi
  have hScale : 0 < value scale := by
    unfold value
    exact div_pos (by exact_mod_cast hScalePositive) (by positivity)
  have hNonzero : Wasm.IEEE32.scaledMagnitude scale ≠ 0 := by
    intro hZero
    simp only [Wasm.IEEE32.scaledValue, hZero, Int.natCast_zero, neg_zero, ite_self] at hScalePositive
    omega
  rw [hCoefficient]
  exact QuantizedScalarError.reconstruction _ _ 156 (by decide) (by decide) hInput hScaleFinite hScale hNonzero hQuotient

#print axioms roundedCoefficient_eq
#print axioms checked_row
#print axioms reconstruction
end Project.ProofKit.QuantizedExport
