import Project.Gpt2QuantizedGroupedRows.ForwardError

namespace Project.Gpt2QuantizedGroupedRows.OutputError
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized Project.ProofKit
open CodeLib.IEEE32 (value)
open ForwardError

structure Bounds where
  scaleBound : Nat → Nat
  outputBound : Nat → Nat
  addBound : Nat → Nat
  biasBound : Nat

def total (weights input : ByteArray) (weightOffset scaleOffset width column : Nat) : UInt32 :=
  sumPrefix weights input weightOffset scaleOffset width 1 0 column (width / 64)

def bias (weights : ByteArray) (biasOffset column : Nat) : UInt32 :=
  LeanExe.Packed.getUInt32LE! weights (biasOffset + column * 4)

structure Ranges (weights input : ByteArray) (weightOffset scaleOffset biasOffset width column : Nat)
    (withBias : Bool) (X W ex ew : Nat → ℝ) (b : Bounds) : Prop where
  groups : ∀ group < width / 64,
    GroupRanges weights input weightOffset scaleOffset width 1 0 column group
      (b.scaleBound group) (b.outputBound group) X W ex ew
  addUpper : ∀ group < width / 64, b.addBound group ≤ 276
  addRange : ∀ group < width / 64,
    (Wasm.IEEE32.scaledValue (sumPrefix weights input weightOffset scaleOffset width 1 0 column group) +
      Wasm.IEEE32.scaledValue (partialValue weights input weightOffset scaleOffset width 1 0 column group)).natAbs < 2 ^ b.addBound group
  biasFinite : withBias = true → CodeLib.IEEE32.Finite (bias weights biasOffset column)
  biasUpper : withBias = true → b.biasBound ≤ 276
  biasRange : withBias = true → (Wasm.IEEE32.scaledValue (total weights input weightOffset scaleOffset width column) +
    Wasm.IEEE32.scaledValue (bias weights biasOffset column)).natAbs < 2 ^ b.biasBound

noncomputable def error (weights input : ByteArray) (weightOffset width column : Nat)
    (withBias : Bool) (X W ex ew : Nat → ℝ) (b : Bounds) : ℝ :=
  (∑ group ∈ Finset.range (width / 64),
    (groupError weights input weightOffset width 1 0 column group X W ex ew
      (b.scaleBound group) (b.outputBound group) + F32AdditionBounds.epsilon (b.addBound group))) +
    if withBias then F32AdditionBounds.epsilon b.biasBound else 0

noncomputable def reference (weights : ByteArray) (biasOffset width column : Nat) (withBias : Bool)
    (X W : Nat → ℝ) : ℝ :=
  (∑ i ∈ Finset.range width, X i * W i) + if withBias then CodeLib.IEEE32.value (bias weights biasOffset column) else 0

theorem output_error (weights input : ByteArray) (weightOffset scaleOffset biasOffset width outputWidth column : Nat)
    (withBias : Bool) (hj : column < outputWidth) (hWidth : 64 ∣ width) (X W ex ew : Nat → ℝ) (b : Bounds)
    (h : Ranges weights input weightOffset scaleOffset biasOffset width column withBias X W ex ew b) :
    CodeLib.IEEE32.Finite (word (linearGroupedRows weights input weightOffset scaleOffset biasOffset width outputWidth 1 withBias) column) ∧
      |CodeLib.IEEE32.value (word (linearGroupedRows weights input weightOffset scaleOffset biasOffset width outputWidth 1 withBias) column) -
        reference weights biasOffset width column withBias X W| ≤ error weights input weightOffset width column withBias X W ex ew b := by
  have hr := row_error weights input weightOffset scaleOffset width 1 0 column hWidth X W ex ew
    b.scaleBound b.outputBound b.addBound h.groups h.addUpper h.addRange
  rw [output_word weights input weightOffset scaleOffset biasOffset width outputWidth 1 column withBias (by simpa using hj)]
  simp only [Gpt2QuantizedGroupedRows.value, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
  cases withBias with
  | false => simpa only [Bool.false_eq_true, ite_false, reference, error, add_zero] using hr
  | true =>
    have hb := bias_error _ (bias weights biasOffset column) _ _ b.biasBound hr.1
      (h.biasFinite rfl) hr.2 (h.biasUpper rfl) (h.biasRange rfl)
    simpa only [reference, error, bias, Bool.true_eq, ite_true, add_comm] using hb

#print axioms output_error
end Project.Gpt2QuantizedGroupedRows.OutputError
