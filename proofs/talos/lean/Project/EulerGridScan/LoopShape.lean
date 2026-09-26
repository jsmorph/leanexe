import Project.EulerGridScan.LoopModel

namespace Project.EulerGridScan.Execution
open Wasm

/-- Derived directly from the generated entry, without a copied instruction cache. -/
def acceptedBody : Wasm.Program :=
  match (func11[19]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ _ body _ _) => body
  | _ => []

def loopCode : Wasm.Program :=
  match (acceptedBody[25]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => body
  | _ => []

theorem first_loop_shape : acceptedBody[25]? = some (.block 0 0 [.loop 0 0 loopCode]) := rfl

#print axioms first_loop_shape
end Project.EulerGridScan.Execution
