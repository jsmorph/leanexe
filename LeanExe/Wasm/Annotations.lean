import Lean.Data.Json.Printer
import LeanExe.IR.Core
import LeanExe.Wasm.Instr
import LeanExe.Wasm.ScalarDescriptor

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

structure FixedArrayFindIdxEqParameters where
  scratchStart : Nat
  sourceWidth : Nat
  inputLocal : Nat
  itemLocal : Nat
  key : String
  resultEncoding : String
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

structure FixedArrayPairResultParameters where
  offset : Nat
  mode : String
  firstValue : Option String
  secondValue : String
  inputIndex : Option Nat
  destination : Nat
  continuation : String
  deriving Repr, Lean.ToJson

structure FixedArrayMapAddParameters where
  maximumSize : Nat
  addend : String
  continuation : String
  deriving Repr, Lean.ToJson

structure FixedArrayFilterLtParameters where
  maximumSize : Nat
  threshold : String
  continuation : String
  deriving Repr, Lean.ToJson

structure LoopFoldParameters where
  resultWidth : Nat
  accumulatorStart : Nat
  accumulatorLocals : Array Nat
  initialValues : Array String
  bodyValues : Array String
  bodyLets : Array String
  doneValue : String
  releaseOffsets : Array Nat
  scratchStart : Nat
  doneLocal : Nat
  stagedValueStart : Nat
  releaseReadyLocal : Nat
  resultLocals : Array Nat
  continuation : String
  deriving Repr, Lean.ToJson

structure ArrayFoldParameters where
  sourceWidth : Nat
  resultWidth : Nat
  reverse : Bool
  array : String
  start : String
  stop : String
  accumulatorStart : Nat
  accumulatorLocals : Array Nat
  itemStart : Nat
  itemLocals : Array Nat
  initialValues : Array String
  bodyValues : Array String
  bodyLets : Array String
  doneValue : String
  releaseOffsets : Array Nat
  descriptorVersion : Nat
  descriptor : Option ScalarDescriptor.PostTest
  scratchStart : Nat
  arrayLocal : Nat
  lengthLocal : Nat
  indexLocal : Nat
  stopLocal : Nat
  effectiveStopLocal : Nat
  doneLocal : Nat
  stagedValueStart : Nat
  releaseReadyLocal : Nat
  resultSlots : Array Nat
  resultLocals : Array Nat
  continuation : String
  deriving Repr, Lean.ToJson

structure WhileLoopParameters where
  condition : String
  body : String
  descriptorVersion : Nat
  descriptor : Option ScalarDescriptor.While
  scratchStart : Nat
  continuation : String
  deriving Repr, Lean.ToJson

structure ScalarPostTestLoopParameters where
  resultWidth : Nat
  accumulatorStart : Nat
  accumulatorLocals : Array Nat
  initialValues : Array String
  resultSlot : Nat
  destination : Nat
  releaseOffsets : Array Nat
  descriptorVersion : Nat
  descriptor : Option ScalarDescriptor.PostTest
  scratchStart : Nat
  continuation : String
  deriving Repr, Lean.ToJson

inductive RegionParameters where
  | directCall (parameters : DirectCallParameters)
  | fixedArrayLengthDispatch (parameters : FixedArrayLengthDispatchParameters)
  | fixedArrayFindIdxEq (parameters : FixedArrayFindIdxEqParameters)
  | fixedArraySearchKey (parameters : FixedArraySearchKeyParameters)
  | fixedArrayEqNode (parameters : FixedArrayEqNodeParameters)
  | fixedArrayLtNode (parameters : FixedArrayLtNodeParameters)
  | fixedArrayPairResult (parameters : FixedArrayPairResultParameters)
  | fixedArrayMapAdd (parameters : FixedArrayMapAddParameters)
  | fixedArrayFilterLt (parameters : FixedArrayFilterLtParameters)
  | loopFold (parameters : LoopFoldParameters)
  | arrayFold (parameters : ArrayFoldParameters)
  | whileLoop (parameters : WhileLoopParameters)
  | scalarPostTestLoop (parameters : ScalarPostTestLoopParameters)
  deriving Repr

instance : Lean.ToJson RegionParameters where
  toJson
    | .directCall parameters => Lean.toJson parameters
    | .fixedArrayLengthDispatch parameters => Lean.toJson parameters
    | .fixedArrayFindIdxEq parameters => Lean.toJson parameters
    | .fixedArraySearchKey parameters => Lean.toJson parameters
    | .fixedArrayEqNode parameters => Lean.toJson parameters
    | .fixedArrayLtNode parameters => Lean.toJson parameters
    | .fixedArrayPairResult parameters => Lean.toJson parameters
    | .fixedArrayMapAdd parameters => Lean.toJson parameters
    | .fixedArrayFilterLt parameters => Lean.toJson parameters
    | .loopFold parameters => Lean.toJson parameters
    | .arrayFold parameters => Lean.toJson parameters
    | .whileLoop parameters => Lean.toJson parameters
    | .scalarPostTestLoop parameters => Lean.toJson parameters

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

structure RelativeFixedArrayFindIdxEq where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  scratchStart : Nat
  sourceWidth : Nat
  inputLocal : Nat
  itemLocal : Nat
  key : String
  resultEncoding : String
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

structure RelativeFixedArrayPairResult where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  offset : Nat
  mode : String
  firstValue : Option String
  secondValue : String
  inputIndex : Option Nat
  destination : Nat
  continuation : String
  generatedBy : Array String
  deriving Repr

structure RelativeArrayFold where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  sourceWidth : Nat
  resultWidth : Nat
  reverse : Bool
  array : String
  start : String
  stop : String
  accumulatorStart : Nat
  accumulatorLocals : Array Nat
  itemStart : Nat
  itemLocals : Array Nat
  initialValues : Array String
  bodyValues : Array String
  bodyLets : Array String
  doneValue : String
  releaseOffsets : Array Nat
  descriptorVersion : Nat
  descriptor : Option ScalarDescriptor.PostTest
  scratchStart : Nat
  arrayLocal : Nat
  lengthLocal : Nat
  indexLocal : Nat
  stopLocal : Nat
  effectiveStopLocal : Nat
  doneLocal : Nat
  stagedValueStart : Nat
  releaseReadyLocal : Nat
  resultSlots : Array Nat
  resultLocals : Array Nat
  continuation : String
  generatedBy : Array String
  deriving Repr

structure RelativeWhileLoop where
  listPath : Array PathStep
  startIndex : Nat
  endIndex : Nat
  condition : String
  body : String
  descriptorVersion : Nat
  descriptor : Option ScalarDescriptor.While
  scratchStart : Nat
  continuation : String
  generatedBy : Array String
  deriving Repr

structure Emitted where
  code : List LeanExe.Wasm.Instr
  directCalls : Array RelativeDirectCall
  lengthDispatches : Array RelativeFixedArrayLengthDispatch
  findIdxEqs : Array RelativeFixedArrayFindIdxEq
  pairResults : Array RelativeFixedArrayPairResult
  arrayFolds : Array RelativeArrayFold
  whileLoops : Array RelativeWhileLoop
  deriving Repr, Inhabited

def Emitted.ofCode (code : List LeanExe.Wasm.Instr) : Emitted :=
  { code
    directCalls := #[]
    lengthDispatches := #[]
    findIdxEqs := #[]
    pairResults := #[]
    arrayFolds := #[]
    whileLoops := #[] }

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
            { step with instructionIndex := offset + step.instructionIndex } }
    findIdxEqs := left.findIdxEqs ++ right.findIdxEqs.map fun findIdx =>
      if h : findIdx.listPath.size = 0 then
        { findIdx with
          startIndex := offset + findIdx.startIndex
          endIndex := offset + findIdx.endIndex }
      else
        let step := findIdx.listPath[0]
        { findIdx with
          listPath := findIdx.listPath.set 0
            { step with instructionIndex := offset + step.instructionIndex } }
    pairResults := left.pairResults ++ right.pairResults.map fun result =>
      if h : result.listPath.size = 0 then
        { result with
          startIndex := offset + result.startIndex
          endIndex := offset + result.endIndex }
      else
        let step := result.listPath[0]
        { result with
          listPath := result.listPath.set 0
            { step with instructionIndex := offset + step.instructionIndex } }
    arrayFolds := left.arrayFolds ++ right.arrayFolds.map fun fold =>
      if h : fold.listPath.size = 0 then
        { fold with
          startIndex := offset + fold.startIndex
          endIndex := offset + fold.endIndex }
      else
        let step := fold.listPath[0]
        { fold with
          listPath := fold.listPath.set 0
            { step with instructionIndex := offset + step.instructionIndex } }
    whileLoops := left.whileLoops ++ right.whileLoops.map fun loop =>
      if h : loop.listPath.size = 0 then
        { loop with
          startIndex := offset + loop.startIndex
          endIndex := offset + loop.endIndex }
      else
        let step := loop.listPath[0]
        { loop with
          listPath := loop.listPath.set 0
            { step with instructionIndex := offset + step.instructionIndex } } }

def render (document : Document) : String :=
  Lean.Json.compress (Lean.toJson document) ++ "\n"

end LeanExe.Wasm.Annotations
