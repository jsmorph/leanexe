import Project.Gpt2QuantizedCached.GroupedProjection.Helpers
import Project.Gpt2QuantizedGroupedRows.Source

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.GroupedProjection.Projection
open Wasm Project.ProofKit LeanExe.Models.Gpt2.Quantized

def parameters (weightsOwner weightsPtr inputOwner inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) : List Wasm.Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size), .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
    .i64 (UInt64.ofNat weightOffset), .i64 (UInt64.ofNat scaleOffset), .i64 (UInt64.ofNat biasOffset),
    .i64 (UInt64.ofNat width), .i64 (UInt64.ofNat outputWidth), .i64 (UInt64.ofNat rows),
    .i64 (if withBias then 1 else 0)]

def outputBody : Wasm.Program :=
  match (func8[99]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def outputWord : Wasm.Program := (outputBody.drop 12).take (outputBody.length - 19)

def branch (withBias : Bool) : Wasm.Program :=
  match (outputWord[7]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes no _ _) => if withBias then yes else no
  | _ => []

def groupBody (withBias : Bool) : Wasm.Program :=
  match ((branch withBias)[10]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def groupStep (withBias : Bool) : Wasm.Program :=
  ((groupBody withBias).drop 4).take ((groupBody withBias).length - 5)

theorem emitted_output : (func8.drop 99).take 1 = PackedGenerateLoop.program 32 95 96 outputWord := rfl

theorem emitted_groups (withBias : Bool) :
    branch withBias = (branch withBias).take 10 ++
      RangeFoldLoop.program 97 98 (groupStep withBias) ++ (branch withBias).drop 11 := by
  cases withBias <;> rfl

def OutputState (params : List Wasm.Value) (valuePtr scalePtr : UInt64)
    (width outputWidth rows : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 100 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (width / 64))) ∧
  frame.locals[6]? = some (.i64 valuePtr) ∧ frame.locals[9]? = some (.i64 scalePtr) ∧
  frame.locals[12]? = some (.i64 valuePtr) ∧ frame.locals[13]? = some (.i64 valuePtr) ∧
  frame.locals[14]? = some (.i64 (UInt64.ofNat (rows * width))) ∧
  frame.locals[15]? = some (.i64 scalePtr) ∧ frame.locals[16]? = some (.i64 scalePtr) ∧
  frame.locals[17]? = some (.i64 (UInt64.ofNat (4 * (rows * (width / 64))))) ∧
  frame.locals[18]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))) ∧ I64Values frame.locals

def Accumulator (weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index group : Nat)
    (withBias : Bool) (frame : Locals) : Prop :=
  OutputState (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset scaleOffset biasOffset
    width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows frame ∧
  frame.locals[if withBias then 21 else 50]? = some (.i64
    (sumPrefix weights input weightOffset scaleOffset width rows
      (index / outputWidth) (index % outputWidth) group).toUInt64) ∧
  frame.locals[86]? = some (.i64 1)

def StepState (weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index group : Nat)
    (withBias : Bool) (frame : Locals) : Prop :=
  Accumulator weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr weights input weightOffset scaleOffset biasOffset
    width outputWidth rows index group withBias frame ∧
  frame.locals[if withBias then 22 else 51]? = some (.i64 (UInt64.ofNat group)) ∧
  frame.locals[if withBias then 23 else 52]? = some (.i64
    (sumPrefix weights input weightOffset scaleOffset width rows
      (index / outputWidth) (index % outputWidth) group).toUInt64)

end Project.Gpt2QuantizedCached.GroupedProjection.Projection
