import Project.Beck.ExecutionDirectionReplicate
import Project.Beck.ExecutionWordSet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionSetFirst : Wasm.Program := match (directionEligible[65]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def directionBody : Wasm.Program := match (directionEligible[85]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def directionSetColumn : Wasm.Program := match (directionBody[25]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def directionSetCoefficient : Wasm.Program := match (directionBody[89]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 4096 in
theorem direction_set_shapes : directionSetFirst.drop 4 = wordSetProgram 98 ∧
    directionSetColumn.drop 4 = wordSetProgram 101 ∧ directionSetCoefficient.drop 4 = wordSetProgram 101 := ⟨rfl, rfl, rfl⟩

end Project.Beck.Execution
