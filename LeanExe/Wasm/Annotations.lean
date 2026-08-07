import Lean.Data.Json.Printer
import LeanExe.IR.Core
import LeanExe.Wasm.Instr

namespace LeanExe.Wasm.Annotations

structure PathStep where
  instructionIndex : Nat
  field : String
  deriving Repr, BEq, Lean.ToJson

structure InstructionLocation where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  deriving Repr, Lean.ToJson

structure DirectCallParameters where
  calleeIndex : Nat
  argumentLocals : Array (Option Nat)
  resultLocals : Array Nat
  resultPlacement : String
  continuation : String
  deriving Repr, Lean.ToJson

structure FixedArrayLengthDispatchParameters where
  inputLocal : Nat
  expectedSize : Nat
  encoding : String
  invalidBranch : String
  validBranch : String
  continuation : String
  deriving Repr, Lean.ToJson

structure FixedArraySearchKeyParameters where
  offset : Nat
  index : Nat
  keyLocal : Nat
  continuation : String
  deriving Repr, Lean.ToJson

structure FixedArrayEqNodeParameters where
  offset : Nat
  index : Nat
  keyLocal : Nat
  operandOrder : String
  equalBranch : String
  unequalBranch : String
  continuation : String
  deriving Repr, Lean.ToJson

structure FixedArrayLtNodeParameters where
  offset : Nat
  index : Nat
  keyLocal : Nat
  operandOrder : String
  comparison : String
  lessBranch : String
  notLessBranch : String
  continuation : String
  deriving Repr, Lean.ToJson

inductive RegionParameters where
  | directCall (parameters : DirectCallParameters)
  | fixedArrayLengthDispatch (parameters : FixedArrayLengthDispatchParameters)
  | fixedArraySearchKey (parameters : FixedArraySearchKeyParameters)
  | fixedArrayEqNode (parameters : FixedArrayEqNodeParameters)
  | fixedArrayLtNode (parameters : FixedArrayLtNodeParameters)
  deriving Repr

instance : Lean.ToJson RegionParameters where
  toJson
    | .directCall parameters => Lean.toJson parameters
    | .fixedArrayLengthDispatch parameters => Lean.toJson parameters
    | .fixedArraySearchKey parameters => Lean.toJson parameters
    | .fixedArrayEqNode parameters => Lean.toJson parameters
    | .fixedArrayLtNode parameters => Lean.toJson parameters

structure Region where
  id : String
  kind : String
  location : InstructionLocation
  parameters : RegionParameters
  generatedBy : Array String
  deriving Repr, Lean.ToJson

structure Function where
  wasmIndex : Nat
  definedFunction : Nat
  sourceName : String
  exports : Array String
  parameters : Nat
  results : Nat
  locals : Nat
  regions : Array Region
  deriving Repr, Lean.ToJson

structure Artifact where
  byteLength : Nat
  deriving Repr, Lean.ToJson

structure Document where
  schemaVersion : Nat
  artifact : Artifact
  functions : Array Function
  deriving Repr, Lean.ToJson

structure RelativeDirectCall where
  listPath : Array PathStep
  startIndex : Nat
  callIndex : Nat
  endIndex : Nat
  calleeIndex : Nat
  argumentLocals : Array (Option Nat)
  resultLocals : Array Nat
  resultPlacement : String
  continuation : String
  generatedBy : Array String
  deriving Repr

structure RelativeFixedArrayLengthDispatch where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  inputLocal : Nat
  expectedSize : Nat
  encoding : String
  invalidBranch : String
  validBranch : String
  continuation : String
  generatedBy : Array String
  deriving Repr

structure RelativeFixedArraySearchKey where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  offset : Nat
  index : Nat
  keyLocal : Nat
  continuation : String
  generatedBy : Array String
  deriving Repr

structure RelativeFixedArrayEqNode where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  offset : Nat
  index : Nat
  keyLocal : Nat
  operandOrder : String
  equalBranch : String
  unequalBranch : String
  continuation : String
  generatedBy : Array String
  deriving Repr

structure RelativeFixedArrayLtNode where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  offset : Nat
  index : Nat
  keyLocal : Nat
  operandOrder : String
  comparison : String
  lessBranch : String
  notLessBranch : String
  continuation : String
  generatedBy : Array String
  deriving Repr

structure Emitted where
  code : List LeanExe.Wasm.Instr
  directCalls : Array RelativeDirectCall
  lengthDispatches : Array RelativeFixedArrayLengthDispatch
  deriving Repr, Inhabited

def Emitted.ofCode (code : List LeanExe.Wasm.Instr) : Emitted :=
  { code, directCalls := #[], lengthDispatches := #[] }

def Emitted.append (left right : Emitted) : Emitted :=
  let offset := left.code.length
  { code := left.code ++ right.code
    directCalls := left.directCalls ++ right.directCalls.map fun call =>
      if h : call.listPath.size = 0 then
        { call with
          startIndex := offset + call.startIndex
          callIndex := offset + call.callIndex
          endIndex := offset + call.endIndex }
      else
        let step := call.listPath[0]
        { call with
          listPath := call.listPath.set 0
            { step with instructionIndex := offset + step.instructionIndex } }
    lengthDispatches := left.lengthDispatches ++ right.lengthDispatches.map fun dispatch =>
      if h : dispatch.listPath.size = 0 then
        { dispatch with
          startIndex := offset + dispatch.startIndex
          endIndex := offset + dispatch.endIndex }
      else
        let step := dispatch.listPath[0]
        { dispatch with
          listPath := dispatch.listPath.set 0
            { step with instructionIndex := offset + step.instructionIndex } } }

def render (document : Document) : String :=
  Lean.Json.compress (Lean.toJson document) ++ "\n"

end LeanExe.Wasm.Annotations
