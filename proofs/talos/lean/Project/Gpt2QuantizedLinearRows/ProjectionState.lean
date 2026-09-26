import Project.Gpt2QuantizedLinearRows.Rows
import Project.Gpt2QuantizedLinearRows.Dot

namespace Project.Gpt2QuantizedLinearRows.Projection
open Wasm Project.ProofKit LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

def parameters (weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) : List Wasm.Value :=
  [.i64 weightsPtr, .i64 (UInt64.ofNat weights.size), .i64 inputPtr, .i64 (UInt64.ofNat input.size),
    .i64 (UInt64.ofNat weightOffset), .i64 (UInt64.ofNat scaleOffset), .i64 (UInt64.ofNat biasOffset),
    .i64 (UInt64.ofNat width), .i64 (UInt64.ofNat outputWidth), .i64 (UInt64.ofNat rows),
    .i64 (if withBias then 1 else 0)]

def value (weights input : ByteArray) (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat)
    (withBias : Bool) : UInt32 :=
  let quantized := quantizeRows input width rows
  let row := index / outputWidth
  let column := index % outputWidth
  let accumulator := dot weights quantized.values (weightOffset + column * width) (row * width) width
  let output := rescale accumulator (word quantized.scales row)
    (LeanExe.Packed.getUInt32LE! weights (scaleOffset + column * 4))
  if withBias then LeanExe.Float32.addBits output
    (LeanExe.Packed.getUInt32LE! weights (biasOffset + column * 4)) else output

theorem linearRows_eq (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) :
    Quantized.linearRows weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias =
      LeanExe.Packed.generateUInt32LE (rows * outputWidth)
        (fun index => value weights input weightOffset scaleOffset biasOffset width outputWidth rows index withBias) := rfl

def outputBody : Wasm.Program :=
  match (func8[83]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def outputWord : Wasm.Program := (outputBody.drop 12).take (outputBody.length - 19)

def branch (withBias : Bool) : Wasm.Program :=
  match (outputWord[7]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes no _ _) => if withBias then yes else no
  | _ => []

theorem emitted_output : (func8.drop 83).take 1 = PackedGenerateLoop.program 29 72 73 outputWord := rfl

def OutputState (params : List Wasm.Value) (valuePtr scalePtr : UInt64)
    (width outputWidth rows : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 73 ∧
  frame.locals[5]? = some (.i64 valuePtr) ∧ frame.locals[8]? = some (.i64 scalePtr) ∧
  frame.locals[11]? = some (.i64 valuePtr) ∧ frame.locals[12]? = some (.i64 valuePtr) ∧
  frame.locals[13]? = some (.i64 (UInt64.ofNat (rows * width))) ∧
  frame.locals[14]? = some (.i64 scalePtr) ∧ frame.locals[15]? = some (.i64 scalePtr) ∧
  frame.locals[16]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧
  frame.locals[17]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))) ∧ I64Values frame.locals

theorem weight_index_bound (weightOffset width outputWidth index size : Nat)
    (hSize : weightOffset + width * outputWidth ≤ size) (hOut : 0 < outputWidth) :
    weightOffset + (index % outputWidth) * width + width ≤ size := by
  have hc := Nat.mod_lt index hOut
  have hm := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hc)
  simp only [Nat.succ_mul] at hm
  nlinarith

theorem input_index_bound (width outputWidth rows index : Nat) (hIndex : index < rows * outputWidth) :
    (index / outputWidth) * width + width ≤ rows * width := by
  have hOut : 0 < outputWidth := by nlinarith
  have hr : index / outputWidth < rows := (Nat.div_lt_iff_lt_mul hOut).mpr hIndex
  exact (Nat.succ_mul _ _).symm ▸ Nat.mul_le_mul_right width (Nat.succ_le_of_lt hr)

theorem scale_index_bound (scaleOffset outputWidth index size : Nat)
    (hSize : scaleOffset + outputWidth * 4 ≤ size) (hOut : 0 < outputWidth) :
    scaleOffset + (index % outputWidth) * 4 + 4 ≤ size := by
  have := Nat.mod_lt index hOut
  omega

end Project.Gpt2QuantizedLinearRows.Projection
