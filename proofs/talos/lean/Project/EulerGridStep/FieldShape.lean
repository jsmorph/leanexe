import Project.EulerGridStep.Program
import Project.EulerGridStep.CopyLoop

namespace Project.EulerGridStep.Execution
open Wasm

/-- The accepted array-write branch is extracted from the generated function. -/
def fieldAcceptedBody : Wasm.Program :=
  match (func27[44]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

/-- This exact emitted region is covered by copy_loop_spec. -/
theorem field_copy_shape : (fieldAcceptedBody.drop 43).take 3 =
    Project.ProofKit.FixedArrayCopy.prefixProgram 10 14 13 15 := rfl

#print axioms field_copy_shape
end Project.EulerGridStep.Execution
