import Project.Gpt2LinearRows.Source
import Project.ProofKit.F32DotRanges
import Project.Gpt2CachedStep.LayerNorm.Numerical
import Project.Gpt2CachedStep.Vocabulary.Source

namespace Project.Gpt2LinearRows.Error
open LeanExe.Models.Gpt2 Project.ProofKit
open Gpt2CachedStep.LayerNorm.Numerical (word_generate)
open CodeLib.IEEE32 (value)

def inputWord (input : ByteArray) (i : Nat) : UInt32 := word input i

def weightWord (weights : ByteArray) (weightOffset outputWidth column i : Nat) : UInt32 :=
  word weights (weightOffset + i * outputWidth + column)

theorem dot_compute (weights input : ByteArray) (weightOffset width outputWidth column count : Nat) :
    dotPrefix weights input weightOffset width outputWidth 0 column count =
      F32DotError.compute (inputWord input) (weightWord weights weightOffset outputWidth column) count := by
  simp only [dotPrefix, F32DotError.compute, F32SumError.sumPrefix, inputWord, weightWord, Nat.zero_mul, Nat.zero_add]

theorem output_source (weights input : ByteArray) (weightOffset biasOffset width outputWidth column : Nat)
    (hj : column < outputWidth) :
    word (linearRows weights input weightOffset biasOffset width outputWidth 1) column =
      LeanExe.Float32.addBits (F32DotError.compute (inputWord input) (weightWord weights weightOffset outputWidth column) width)
        (word weights (biasOffset + column)) := by
  rw [linearRows_eq, word_generate _ _ column (by simpa using hj)]
  simp only [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Gpt2LinearRows.value, dot_compute, F32Add.add_eq]

theorem output_error (weights input : ByteArray) (weightOffset biasOffset width outputWidth column : Nat)
    (hj : column < outputWidth) (X W ex ew : Nat → ℝ) (b : F32DotError.Bounds) (biasBound : Nat)
    (h : F32DotError.Ranges (inputWord input) (weightWord weights weightOffset outputWidth column) width b)
    (hx : ∀ i < width, |CodeLib.IEEE32.value (inputWord input i) - X i| ≤ ex i)
    (hw : ∀ i < width, |CodeLib.IEEE32.value (weightWord weights weightOffset outputWidth column i) - W i| ≤ ew i)
    (hb : CodeLib.IEEE32.Finite (word weights (biasOffset + column)))
    (hbu : biasBound ≤ 276)
    (hbr : (Wasm.IEEE32.scaledValue (F32DotError.compute (inputWord input)
      (weightWord weights weightOffset outputWidth column) width) + Wasm.IEEE32.scaledValue (word weights (biasOffset + column))).natAbs < 2 ^ biasBound) :
    CodeLib.IEEE32.Finite (word (linearRows weights input weightOffset biasOffset width outputWidth 1) column) ∧
      |CodeLib.IEEE32.value (word (linearRows weights input weightOffset biasOffset width outputWidth 1) column) -
        ((∑ i ∈ Finset.range width, X i * W i) + CodeLib.IEEE32.value (word weights (biasOffset + column)))| ≤
      F32AdditionBounds.epsilon biasBound + F32DotError.errorBound (inputWord input) W ex ew width b := by
  rw [output_source weights input weightOffset biasOffset width outputWidth column hj]
  have hd := F32DotError.error_of_ranges _ _ X W ex ew width b h hx hw
  have ha := F32ErrorPropagation.add _ _ _ (CodeLib.IEEE32.value (word weights (biasOffset + column))) _ 0 biasBound hd.1 hb hbu hbr hd.2 (by simp)
  simpa only [add_zero] using ha

theorem vocabulary_source (weights input : ByteArray) (token : Nat) (ht : token < 50257) :
    word (vocabularyHead weights input) token =
      F32DotError.compute (word input) (fun i => word weights (token * 768 + i)) 768 := by
  rw [Gpt2CachedStep.Vocabulary.vocabularyHead_eq, word_generate _ _ token ht]
  rfl

#print axioms output_error
#print axioms vocabulary_source
end Project.Gpt2LinearRows.Error
