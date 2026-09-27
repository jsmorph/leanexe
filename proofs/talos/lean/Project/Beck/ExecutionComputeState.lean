import Project.Beck.ExecutionInput
import Project.Beck.ExecutionWordUpdate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def computeAccepted : Wasm.Program := match (func35[40]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def computeOutput : Wasm.Program := match (computeAccepted[148]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def computeOutputBody : Wasm.Program := match (computeOutput[83]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

structure ComputeInputLocals (locals : List Value) (input : Input) (owner root : UInt64) : Prop where
  size : locals.length = 79
  words : WordLocals locals
  status : locals[8]? = some (.i64 input.status)
  jobs : locals[9]? = some (.i64 input.jobs.toUInt64)
  categories : locals[10]? = some (.i64 input.categories.toUInt64)
  overlap : locals[11]? = some (.i64 input.overlap.toUInt64)
  owner : locals[12]? = some (.i64 owner)
  pointer : locals[13]? = some (.i64 root)

end Project.Beck.Execution
