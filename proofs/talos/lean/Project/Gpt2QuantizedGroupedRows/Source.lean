import LeanExe.Models.Gpt2.Quantized.Grouped
import Project.Gpt2QuantizedLinearRows.Source

namespace Project.Gpt2QuantizedGroupedRows
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized LeanExe.Signed32 Project.ProofKit

def partialValue (weights input : ByteArray)
    (weightOffset scaleOffset width rows row column group : Nat) : UInt32 :=
  let quantized := quantizeRows input 64 (rows * (width / 64))
  rescale (dot weights quantized.values (weightOffset + column * width + group * 64)
    (row * width + group * 64) 64)
    (word quantized.scales (row * (width / 64) + group))
    (LeanExe.Packed.getUInt32LE! weights (scaleOffset + column * 4))

def sumPrefix (weights input : ByteArray)
    (weightOffset scaleOffset width rows row column count : Nat) : UInt32 :=
  (List.range count).foldl (fun total group => LeanExe.Float32.addBits total
    (partialValue weights input weightOffset scaleOffset width rows row column group)) 0

@[simp] theorem sumPrefix_zero (weights input : ByteArray)
    (weightOffset scaleOffset width rows row column : Nat) :
    sumPrefix weights input weightOffset scaleOffset width rows row column 0 = 0 := rfl

theorem sumPrefix_succ (weights input : ByteArray)
    (weightOffset scaleOffset width rows row column count : Nat) :
    sumPrefix weights input weightOffset scaleOffset width rows row column (count + 1) =
      LeanExe.Float32.addBits
        (sumPrefix weights input weightOffset scaleOffset width rows row column count)
        (partialValue weights input weightOffset scaleOffset width rows row column count) := by
  simp only [sumPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

def value (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat) (withBias : Bool) : UInt32 :=
  let total := sumPrefix weights input weightOffset scaleOffset width rows
    (index / outputWidth) (index % outputWidth) (width / 64)
  if withBias then LeanExe.Float32.addBits total
    (LeanExe.Packed.getUInt32LE! weights (biasOffset + (index % outputWidth) * 4)) else total

theorem linearGroupedRows_eq (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) :
    linearGroupedRows weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias =
      LeanExe.Packed.generateUInt32LE (rows * outputWidth)
        (fun index => value weights input weightOffset scaleOffset biasOffset width outputWidth rows index withBias) := by
  simp only [linearGroupedRows, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem grouped_values_size (input : ByteArray) (width rows : Nat) (hw : 64 ∣ width) :
    (quantizeRows input 64 (rows * (width / 64))).values.size = rows * width := by
  rw [Project.Gpt2QuantizedLinearRows.quantized_values_size, Nat.mul_assoc,
    Nat.div_mul_cancel hw]

theorem grouped_scales_size (input : ByteArray) (width rows : Nat) :
    (quantizeRows input 64 (rows * (width / 64))).scales.size = 4 * (rows * (width / 64)) := by
  exact Project.Gpt2QuantizedLinearRows.quantized_scales_size _ _ _

theorem linearGroupedRows_size (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) :
    (linearGroupedRows weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias).size = 4 * (rows * outputWidth) := by
  exact PackedSource.generate_size _ _

theorem grouped_dot_prefix (weights input : ByteArray)
    (weightOffset width outputWidth rows row column group count : Nat)
    (hw : 64 ∣ width) (hr : row < rows) (hj : column < outputWidth)
    (hg : group < width / 64) (hc : count ≤ 64)
    (weightsValid : ∀ i < outputWidth * width, weights[weightOffset + i]! ≠ 128) :
    let values := (quantizeRows input 64 (rows * (width / 64))).values
    let inputOffset := row * width + group * 64
    let offset := weightOffset + column * width + group * 64
    decode (dot weights values offset inputOffset count) =
      QuantizedInt32.sumPrefix
        (fun i => decode (extend8Bits values[inputOffset + i]!.toUInt32))
        (fun i => decode (extend8Bits weights[offset + i]!.toUInt32)) count ∧
    |decode (dot weights values offset inputOffset count)| ≤ (count : Int) * 16129 := by
  dsimp only
  have hWidth : width / 64 * 64 = width := Nat.div_mul_cancel hw
  have hGroup : group * 64 + 64 ≤ width := by omega
  have hInput : ∀ i < count,
      (quantizeRows input 64 (rows * (width / 64))).values[row * width + group * 64 + i]! ≠ 128 := by
    intro i hi
    apply QuantizedValue.quantizeRows_valid
    rw [Nat.mul_assoc, hWidth]
    have := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hr)
    nlinarith
  have hWeights : ∀ i < count,
      weights[weightOffset + column * width + group * 64 + i]! ≠ 128 := by
    intro i hi
    have := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hj)
    have hb : column * width + group * 64 + i < outputWidth * width := by nlinarith
    simpa only [Nat.add_assoc] using weightsValid (column * width + group * 64 + i) hb
  exact ⟨QuantizedDot.dot_exact _ _ _ _ _ (by omega) hInput hWeights,
    QuantizedDot.dot_prefix_range _ _ _ _ _ (by omega) hInput hWeights⟩

theorem group_accumulator_bound (weights values : ByteArray) (weightOffset inputOffset count : Nat)
    (hc : count ≤ 64)
    (inputValid : ∀ i < count, values[inputOffset + i]! ≠ 128)
    (weightsValid : ∀ i < count, weights[weightOffset + i]! ≠ 128) :
    |decode (dot weights values weightOffset inputOffset count)| ≤ 1032256 := by
  have h := QuantizedDot.dot_prefix_range weights values weightOffset inputOffset count
    (by omega) inputValid weightsValid
  have hCount : (count : Int) ≤ 64 := by exact_mod_cast hc
  omega

#print axioms grouped_dot_prefix
#print axioms group_accumulator_bound

end Project.Gpt2QuantizedGroupedRows
