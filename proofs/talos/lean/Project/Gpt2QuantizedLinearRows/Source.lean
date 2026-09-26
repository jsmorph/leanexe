import Project.ProofKit.QuantizedDot
import Project.ProofKit.QuantizedValue
import Project.ProofKit.PackedSource

namespace Project.Gpt2QuantizedLinearRows
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized LeanExe.Signed32 Project.ProofKit

theorem quantized_values_size (input : ByteArray) (width rows : Nat) :
    (quantizeRows input width rows).values.size = rows * width := by
  exact PackedByteSource.generate_size _ _

theorem quantized_scales_size (input : ByteArray) (width rows : Nat) :
    (quantizeRows input width rows).scales.size = 4 * rows := by
  exact PackedSource.generate_size _ _

theorem quantized_scale_read (input : ByteArray) (width rows row : Nat) (hr : row < rows) :
    word (quantizeRows input width rows).scales row = rowScale input (row * width) width := by
  unfold quantizeRows word
  rw [Nat.mul_comm row 4, PackedSource.generate_read _ _ _ hr]

theorem quantized_value_read (input : ByteArray) (width rows index : Nat)
    (hi : index < rows * width) :
    (quantizeRows input width rows).values[index]! =
      quantizeValue (word input index) (rowScale input (index / width * width) width) := by
  have hw : 0 < width := by nlinarith
  have hr : index / width < rows := (Nat.div_lt_iff_lt_mul hw).mpr hi
  change (LeanExe.Packed.generateUInt8 (rows * width) _)[index]! = _
  rw [PackedByteSource.generate_byte _ _ _ hi]
  change quantizeValue (word input index) (word (quantizeRows input width rows).scales (index / width)) = _
  rw [quantized_scale_read input width rows (index / width) hr]

theorem quantized_dot_prefix (weights input : ByteArray)
    (weightOffset width rows row count : Nat)
    (hw : width ≤ 3072) (hr : row < rows) (hc : count ≤ width)
    (weightsValid : ∀ i < count, weights[weightOffset + i]! ≠ 128) :
    decode (dot weights (quantizeRows input width rows).values weightOffset (row * width) count) =
      QuantizedInt32.sumPrefix
        (fun i => decode (extend8Bits (quantizeRows input width rows).values[row * width + i]!.toUInt32))
        (fun i => decode (extend8Bits weights[weightOffset + i]!.toUInt32)) count ∧
    |decode (dot weights (quantizeRows input width rows).values weightOffset (row * width) count)| ≤
      (count : Int) * 16129 := by
  have inputValid : ∀ i < count,
      (quantizeRows input width rows).values[row * width + i]! ≠ 128 := by
    intro i hi
    apply QuantizedValue.quantizeRows_valid
    nlinarith
  exact ⟨QuantizedDot.dot_exact _ _ _ _ _ (by omega) inputValid weightsValid,
    QuantizedDot.dot_prefix_range _ _ _ _ _ (by omega) inputValid weightsValid⟩

theorem linearRows_size (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) :
    (Quantized.linearRows weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias).size = 4 * (rows * outputWidth) := by
  exact PackedSource.generate_size _ _

theorem projection_dot_prefix (weights input : ByteArray)
    (weightOffset width outputWidth rows row column count : Nat)
    (hw : width ≤ 3072) (hr : row < rows) (hj : column < outputWidth) (hc : count ≤ width)
    (weightsValid : ∀ i < outputWidth * width, weights[weightOffset + i]! ≠ 128) :
    decode (dot weights (quantizeRows input width rows).values
      (weightOffset + column * width) (row * width) count) =
      QuantizedInt32.sumPrefix
        (fun i => decode (extend8Bits (quantizeRows input width rows).values[row * width + i]!.toUInt32))
        (fun i => decode (extend8Bits weights[weightOffset + column * width + i]!.toUInt32)) count ∧
    |decode (dot weights (quantizeRows input width rows).values
      (weightOffset + column * width) (row * width) count)| ≤ (count : Int) * 16129 := by
  apply quantized_dot_prefix weights input (weightOffset + column * width) width rows row count hw hr hc
  intro i hi
  have hBound : column * width + i < outputWidth * width := by nlinarith
  simpa only [Nat.add_assoc] using weightsValid (column * width + i) hBound

#print axioms quantized_dot_prefix
#print axioms projection_dot_prefix

end Project.Gpt2QuantizedLinearRows
