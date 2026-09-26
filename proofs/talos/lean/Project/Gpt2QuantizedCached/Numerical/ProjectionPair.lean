import Project.Gpt2QuantizedGroupedRows.OutputError
import Project.Gpt2LinearRows.Error

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionPair
open LeanExe.Models.Gpt2 Project.ProofKit
open CodeLib.IEEE32 (value)

structure Layout where
  qWeight : Nat
  qScale : Nat
  qBias : Nat
  rWeight : Nat
  rBias : Nat
  width : Nat
  outputWidth : Nat

noncomputable def inputValues (input : ByteArray) : Nat → ℝ := fun i => value (word input i)
noncomputable def weightValues (weights : ByteArray) (l : Layout) (column : Nat) : Nat → ℝ :=
  fun i => value (Gpt2LinearRows.Error.weightWord weights l.rWeight l.outputWidth column i)

structure Bounds where
  quantized : Gpt2QuantizedGroupedRows.OutputError.Bounds
  reference : F32DotError.Bounds
  biasBound : Nat

structure Ranges (qw qi rw ri : ByteArray) (l : Layout) (column : Nat)
    (activationError weightError : Nat → ℝ) (b : Bounds) : Prop where
  quantized : Gpt2QuantizedGroupedRows.OutputError.Ranges qw qi l.qWeight l.qScale l.qBias l.width column true
    (inputValues qi) (weightValues rw l column) activationError weightError b.quantized
  reference : F32DotError.Ranges (Gpt2LinearRows.Error.inputWord ri)
    (Gpt2LinearRows.Error.weightWord rw l.rWeight l.outputWidth column) l.width b.reference
  biasEqual : Gpt2QuantizedGroupedRows.OutputError.bias qw l.qBias column = word rw (l.rBias + column)
  biasFinite : CodeLib.IEEE32.Finite (word rw (l.rBias + column))
  biasUpper : b.biasBound ≤ 276
  biasRange : (Wasm.IEEE32.scaledValue (F32DotError.compute (Gpt2LinearRows.Error.inputWord ri)
    (Gpt2LinearRows.Error.weightWord rw l.rWeight l.outputWidth column) l.width) +
      Wasm.IEEE32.scaledValue (word rw (l.rBias + column))).natAbs < 2 ^ b.biasBound

theorem transfer_input (qw qi : ByteArray) (l : Layout) (column : Nat) (withBias : Bool)
    (X Y W ex ey ew : Nat → ℝ) (b : Gpt2QuantizedGroupedRows.OutputError.Bounds)
    (h : Gpt2QuantizedGroupedRows.OutputError.Ranges qw qi l.qWeight l.qScale l.qBias l.width column withBias X W ex ew b)
    (he : ∀ i < l.width, |X i - Y i| ≤ ey i) :
    Gpt2QuantizedGroupedRows.OutputError.Ranges qw qi l.qWeight l.qScale l.qBias l.width column withBias
      Y W (fun i => ex i + ey i) ew b := by
  refine ⟨?_, h.addUpper, h.addRange, h.biasFinite, h.biasUpper, h.biasRange⟩
  intro group hg
  have g := h.groups group hg
  refine ⟨g.inputValid, g.weightValid, ?_, g.weightError, g.inputFinite, g.weightFinite,
    g.scaleLower, g.scaleUpper, g.outputLower, g.outputUpper, g.scaleRange, g.outputRange⟩
  intro i hi
  have hIndex : group * 64 + i < l.width := by omega
  exact (abs_sub_le _ (X (group * 64 + i)) _).trans (add_le_add (g.inputError i hi) (he _ hIndex))

noncomputable def error (qw qi rw ri : ByteArray) (l : Layout) (column : Nat)
    (inputError activationError weightError : Nat → ℝ) (b : Bounds) : ℝ :=
  Gpt2QuantizedGroupedRows.OutputError.error qw qi l.qWeight l.width column true (inputValues ri)
    (weightValues rw l column) (fun i => activationError i + inputError i) weightError b.quantized +
    (F32AdditionBounds.epsilon b.biasBound + F32DotError.errorBound (Gpt2LinearRows.Error.inputWord ri)
      (weightValues rw l column) (fun _ => 0) (fun _ => 0) l.width b.reference)

theorem component_error (qw qi rw ri : ByteArray) (l : Layout) (column : Nat)
    (hc : column < l.outputWidth) (hw : 64 ∣ l.width)
    (inputError activationError weightError : Nat → ℝ) (b : Bounds)
    (h : Ranges qw qi rw ri l column activationError weightError b)
    (he : ∀ i < l.width, |value (word qi i) - value (word ri i)| ≤ inputError i) :
    CodeLib.IEEE32.Finite (word (Quantized.linearGroupedRows qw qi l.qWeight l.qScale l.qBias l.width l.outputWidth 1 true) column) ∧
      CodeLib.IEEE32.Finite (word (linearRows rw ri l.rWeight l.rBias l.width l.outputWidth 1) column) ∧
      |value (word (Quantized.linearGroupedRows qw qi l.qWeight l.qScale l.qBias l.width l.outputWidth 1 true) column) -
        value (word (linearRows rw ri l.rWeight l.rBias l.width l.outputWidth 1) column)| ≤
      error qw qi rw ri l column inputError activationError weightError b := by
  have ht := transfer_input qw qi l column true (inputValues qi) (inputValues ri) (weightValues rw l column)
    activationError inputError weightError b.quantized h.quantized he
  have hq := Gpt2QuantizedGroupedRows.OutputError.output_error qw qi l.qWeight l.qScale l.qBias l.width l.outputWidth column
    true hc hw (inputValues ri) (weightValues rw l column) (fun i => activationError i + inputError i) weightError b.quantized ht
  have hr := Gpt2LinearRows.Error.output_error rw ri l.rWeight l.rBias l.width l.outputWidth column hc
    (inputValues ri) (weightValues rw l column) (fun _ => 0) (fun _ => 0) b.reference b.biasBound
    h.reference (by intro i hi; simp [inputValues, Gpt2LinearRows.Error.inputWord])
    (by intro i hi; simp [weightValues]) h.biasFinite h.biasUpper h.biasRange
  simp only [Gpt2QuantizedGroupedRows.OutputError.reference, Bool.true_eq, ite_true, h.biasEqual] at hq
  exact ⟨hq.1, hr.1, F32ErrorPropagation.compare _ _ _ _ _ hq.2 hr.2⟩

#print axioms transfer_input
#print axioms component_error
end Project.Gpt2QuantizedCached.Numerical.ProjectionPair
