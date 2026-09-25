import Project.Gpt2QuantizedGroupedRows.Source
import Project.ProofKit.QuantizedGroupError
import Project.ProofKit.F32SumError

namespace Project.Gpt2QuantizedGroupedRows
open Project.ProofKit CodeLib.IEEE32

theorem ordered_group_error (weights input : ByteArray)
    (weightOffset scaleOffset width rows row column : Nat)
    (reference error : Nat → ℝ) (bounds : Nat → Nat)
    (hFinite : ∀ group < width / 64,
      Finite (partialValue weights input weightOffset scaleOffset width rows row column group))
    (hError : ∀ group < width / 64,
      |CodeLib.IEEE32.value (partialValue weights input weightOffset scaleOffset width rows row column group) -
        reference group| ≤ error group)
    (hBound : ∀ group < width / 64, bounds group ≤ 276)
    (hRange : ∀ group < width / 64,
      (Wasm.IEEE32.scaledValue (sumPrefix weights input weightOffset scaleOffset width rows row column group) +
        Wasm.IEEE32.scaledValue (partialValue weights input weightOffset scaleOffset width rows row column group)).natAbs <
          2 ^ bounds group) :
    Finite (sumPrefix weights input weightOffset scaleOffset width rows row column (width / 64)) ∧
      |CodeLib.IEEE32.value (sumPrefix weights input weightOffset scaleOffset width rows row column (width / 64)) -
          ∑ group ∈ Finset.range (width / 64), reference group| ≤
        ∑ group ∈ Finset.range (width / 64), (error group + F32AdditionBounds.epsilon (bounds group)) :=
  F32SumError.ordered_error _ reference error bounds (width / 64) hFinite hError hBound hRange

theorem bias_error (total bias : UInt32) (reference error : ℝ) (bound : Nat)
    (hTotal : Finite total) (hBias : Finite bias)
    (hError : |CodeLib.IEEE32.value total - reference| ≤ error)
    (hBound : bound ≤ 276)
    (hRange : (Wasm.IEEE32.scaledValue total + Wasm.IEEE32.scaledValue bias).natAbs < 2 ^ bound) :
    Finite (LeanExe.Float32.addBits total bias) ∧
      |CodeLib.IEEE32.value (LeanExe.Float32.addBits total bias) -
          (reference + CodeLib.IEEE32.value bias)| ≤ F32AdditionBounds.epsilon bound + error := by
  have hAdd := F32AdditionBounds.add_real_error total bias bound hBound hTotal hBias hRange
  rw [← F32Add.add_eq] at hAdd
  refine ⟨hAdd.1, ?_⟩
  have hOperands : |(CodeLib.IEEE32.value total + CodeLib.IEEE32.value bias) -
      (reference + CodeLib.IEEE32.value bias)| ≤ error := by simpa only [add_sub_add_right_eq_sub] using hError
  exact (abs_sub_le _ _ _).trans (add_le_add hAdd.2 hOperands)

theorem output_word (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat) (withBias : Bool)
    (hIndex : index < rows * outputWidth) :
    LeanExe.Models.Gpt2.word (LeanExe.Models.Gpt2.Quantized.linearGroupedRows weights input
      weightOffset scaleOffset biasOffset width outputWidth rows withBias) index =
      value weights input weightOffset scaleOffset biasOffset width outputWidth rows index withBias := by
  rw [linearGroupedRows_eq]
  unfold LeanExe.Models.Gpt2.word
  rw [Nat.mul_comm index 4]
  exact PackedSource.generate_read _ _ index hIndex

#print axioms ordered_group_error
#print axioms bias_error
#print axioms output_word
end Project.Gpt2QuantizedGroupedRows
