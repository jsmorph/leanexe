import Project.Gpt2QuantizedGroupedRows.Error
import Project.ProofKit.F32DotError

namespace Project.Gpt2QuantizedGroupedRows.ForwardError
open Project.ProofKit LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

theorem sum_groups (f : Nat → ℝ) (width groups : Nat) :
    (∑ group ∈ Finset.range groups, ∑ i ∈ Finset.range width, f (group * width + i)) =
      ∑ i ∈ Finset.range (groups * width), f i := by
  induction groups with
  | zero => simp
  | succ groups ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

def inputScale (input : ByteArray) (width rows row group : Nat) : UInt32 :=
  word (quantizeRows input 64 (rows * (width / 64))).scales (row * (width / 64) + group)

def weightScale (weights : ByteArray) (scaleOffset column : Nat) : UInt32 :=
  LeanExe.Packed.getUInt32LE! weights (scaleOffset + column * 4)

def accumulator (weights input : ByteArray) (weightOffset width rows row column group : Nat) : UInt32 :=
  dot weights (quantizeRows input 64 (rows * (width / 64))).values
    (weightOffset + column * width + group * 64) (row * width + group * 64) 64

noncomputable def groupError (weights input : ByteArray)
    (weightOffset width rows row column group : Nat)
    (X W ex ew : Nat → ℝ) (scaleBound outputBound : Nat) : ℝ :=
  F32MultiplicationBounds.epsilon outputBound +
    |(LeanExe.Signed32.decode (accumulator weights input weightOffset width rows row column group) : ℝ)| *
      F32MultiplicationBounds.epsilon scaleBound +
    ∑ i ∈ Finset.range 64, (|W (group * 64 + i)| * ex (group * 64 + i) +
      |X (group * 64 + i)| * ew (group * 64 + i) + ex (group * 64 + i) * ew (group * 64 + i))

structure GroupRanges (weights input : ByteArray)
    (weightOffset scaleOffset width rows row column group scaleBound outputBound : Nat)
    (X W ex ew : Nat → ℝ) : Prop where
  inputValid : ∀ i < 64,
    (quantizeRows input 64 (rows * (width / 64))).values[row * width + group * 64 + i]! ≠ 128
  weightValid : ∀ i < 64, weights[weightOffset + column * width + group * 64 + i]! ≠ 128
  inputError : ∀ i < 64,
    |CodeLib.IEEE32.value (inputScale input width rows row group) *
        QuantizedGroupError.byteValue (quantizeRows input 64 (rows * (width / 64))).values
          (row * width + group * 64 + i) - X (group * 64 + i)| ≤ ex (group * 64 + i)
  weightError : ∀ i < 64,
    |CodeLib.IEEE32.value (weightScale weights scaleOffset column) *
        QuantizedGroupError.byteValue weights (weightOffset + column * width + group * 64 + i) -
      W (group * 64 + i)| ≤ ew (group * 64 + i)
  inputFinite : CodeLib.IEEE32.Finite (inputScale input width rows row group)
  weightFinite : CodeLib.IEEE32.Finite (weightScale weights scaleOffset column)
  scaleLower : 173 ≤ scaleBound
  scaleUpper : scaleBound ≤ 425
  outputLower : 173 ≤ outputBound
  outputUpper : outputBound ≤ 425
  scaleRange : Wasm.IEEE32.scaledMagnitude (inputScale input width rows row group) *
    Wasm.IEEE32.scaledMagnitude (weightScale weights scaleOffset column) < 2 ^ scaleBound
  outputRange : Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.ofInt32Bits
      (accumulator weights input weightOffset width rows row column group)) *
    Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.mulBits
      (inputScale input width rows row group) (weightScale weights scaleOffset column)) < 2 ^ outputBound

theorem partial_error (weights input : ByteArray)
    (weightOffset scaleOffset width rows row column group scaleBound outputBound : Nat)
    (X W ex ew : Nat → ℝ)
    (h : GroupRanges weights input weightOffset scaleOffset width rows row column group
      scaleBound outputBound X W ex ew) :
    CodeLib.IEEE32.Finite (partialValue weights input weightOffset scaleOffset width rows row column group) ∧
      |CodeLib.IEEE32.value (partialValue weights input weightOffset scaleOffset width rows row column group) -
          ∑ i ∈ Finset.range 64, X (group * 64 + i) * W (group * 64 + i)| ≤
        groupError weights input weightOffset width rows row column group X W ex ew scaleBound outputBound :=
  QuantizedGroupError.reconstruction weights (quantizeRows input 64 (rows * (width / 64))).values
    (weightOffset + column * width + group * 64) (row * width + group * 64) 64
    (inputScale input width rows row group) (weightScale weights scaleOffset column)
    (fun i => X (group * 64 + i)) (fun i => W (group * 64 + i))
    (fun i => ex (group * 64 + i)) (fun i => ew (group * 64 + i))
    scaleBound outputBound (by decide) h.inputValid h.weightValid h.inputError h.weightError
    h.inputFinite h.weightFinite h.scaleLower h.scaleUpper h.outputLower h.outputUpper h.scaleRange h.outputRange

theorem row_error (weights input : ByteArray)
    (weightOffset scaleOffset width rows row column : Nat) (hWidth : 64 ∣ width)
    (X W ex ew : Nat → ℝ) (scaleBounds outputBounds addBounds : Nat → Nat)
    (hGroups : ∀ group < width / 64,
      GroupRanges weights input weightOffset scaleOffset width rows row column group
        (scaleBounds group) (outputBounds group) X W ex ew)
    (hAddUpper : ∀ group < width / 64, addBounds group ≤ 276)
    (hAddRange : ∀ group < width / 64,
      (Wasm.IEEE32.scaledValue (sumPrefix weights input weightOffset scaleOffset width rows row column group) +
        Wasm.IEEE32.scaledValue (partialValue weights input weightOffset scaleOffset width rows row column group)).natAbs <
          2 ^ addBounds group) :
    CodeLib.IEEE32.Finite (sumPrefix weights input weightOffset scaleOffset width rows row column (width / 64)) ∧
      |CodeLib.IEEE32.value (sumPrefix weights input weightOffset scaleOffset width rows row column (width / 64)) -
          ∑ i ∈ Finset.range width, X i * W i| ≤
        ∑ group ∈ Finset.range (width / 64),
          (groupError weights input weightOffset width rows row column group X W ex ew
            (scaleBounds group) (outputBounds group) + F32AdditionBounds.epsilon (addBounds group)) := by
  have hPartial (group : Nat) (hg : group < width / 64) :=
    partial_error weights input weightOffset scaleOffset width rows row column group
      (scaleBounds group) (outputBounds group) X W ex ew (hGroups group hg)
  have h := ordered_group_error weights input weightOffset scaleOffset width rows row column
    (fun group => ∑ i ∈ Finset.range 64, X (group * 64 + i) * W (group * 64 + i))
    (fun group => groupError weights input weightOffset width rows row column group X W ex ew
      (scaleBounds group) (outputBounds group)) addBounds
    (fun group hg => (hPartial group hg).1) (fun group hg => (hPartial group hg).2) hAddUpper hAddRange
  rw [sum_groups (fun i => X i * W i), Nat.div_mul_cancel hWidth] at h
  exact h

#print axioms partial_error
#print axioms row_error
end Project.Gpt2QuantizedGroupedRows.ForwardError
