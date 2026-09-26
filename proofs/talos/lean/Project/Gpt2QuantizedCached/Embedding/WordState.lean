import Project.Gpt2QuantizedCached.Layout
import Project.ProofKit.PackedByteAccess
import Project.ProofKit.PackedWordAccess
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame
import Project.ProofKit.CallRemainder
import Project.ProofKit.SignedByte
import Project.ProofKit.F32Convert
import Project.ProofKit.F32Mul
import Project.ProofKit.F32Add

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Embedding
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def parameters (owner ptr : UInt64) (weights : ByteArray) (token : UInt32) (position : Nat) : List Value :=
  [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat weights.size),
    .i64 (UInt64.ofNat token.toNat), .i64 (UInt64.ofNat position)]

def scale (weights : ByteArray) (token : UInt32) : UInt32 :=
  LeanExe.Packed.getUInt32LE! weights (tokenScaleOffset + token.toNat * 4)

def value (weights : ByteArray) (token : UInt32) (position index : Nat) : UInt32 :=
  LeanExe.Float32.addBits
    (LeanExe.Float32.mulBits
      (LeanExe.Float32.ofInt32Bits (LeanExe.Signed32.extend8Bits
        weights[tokenWeightOffset + token.toNat * 768 + index]!.toUInt32)) (scale weights token))
    (LeanExe.Packed.getUInt32LE! weights (positionOffset + (position * 768 + index) * 4))

theorem source_eq (weights : ByteArray) (token : UInt32) (position : Nat) :
    embedding weights token position = LeanExe.Packed.generateUInt32LE 768 (value weights token position) := rfl

def loopBody : Wasm.Program :=
  match (func30[70]? : Option Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def wordCode : Wasm.Program := (loopBody.drop 12).take (loopBody.length - 19)

theorem emitted_loop : (func30.drop 70).take 1 = PackedGenerateLoop.program 7 12 13 wordCode := rfl

def State (params : List Value) (weights : ByteArray) (token : UInt32) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 22 ∧
  frame.locals[0]? = some (.i64 (scale weights token).toUInt64) ∧
  frame.locals[1]? = some (.i64 3072) ∧ I64Values frame.locals

def tokenCode : Wasm.Program := wordCode.take 54
def positionCode : Wasm.Program := wordCode.drop 54

def tokenValue (weights : ByteArray) (token : UInt32) (index : Nat) : UInt32 :=
  Wasm.IEEE32.mul (Wasm.IEEE32.convertI32S (LeanExe.Signed32.extend8Bits
    weights[tokenWeightOffset + token.toNat * 768 + index]!.toUInt32)) (scale weights token)

theorem word_parts : wordCode = tokenCode ++ positionCode := by
  exact (List.take_append_drop 54 wordCode).symm

end Project.Gpt2QuantizedCached.Embedding
