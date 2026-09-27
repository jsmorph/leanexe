import Project.EulerGridStep.WriterShape
import Project.EulerGridStep.CopyUpdate

namespace Project.EulerGridStep.Execution
open Wasm

/-- The in-bounds cloning branch used to set the output's rejection status. -/
def rejectedCloneBody : Wasm.Program :=
  match (writerRejectedBody[17]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

def rejectedPrefix : Wasm.Program :=
  [.localGet 1, .localSet 62, .constI64 0, .localSet 63,
    .localGet 62, .localSet 67, .localGet 63, .localSet 68,
    .constI64 1, .localSet 73, .localGet 67, .wrapI64, .load64 0,
    .localSet 69, .localGet 68, .localGet 69, .ltUI64]

def rejectedFinish : Wasm.Program :=
  [.localSet 64, .localGet 64, .localSet 65, .localGet 64, .localSet 66]

theorem rejected_prefix_shape : writerRejectedBody.take 17 = rejectedPrefix := rfl

theorem rejected_branch_shape : writerRejectedBody = rejectedPrefix ++
    [.iff 0 1 rejectedCloneBody [.unreachable] [] [.i64]] ++ rejectedFinish := rfl

theorem rejected_copy_update_shape : rejectedCloneBody.drop 39 = copyUpdateProgram 67 := rfl

#print axioms rejected_prefix_shape
#print axioms rejected_branch_shape
#print axioms rejected_copy_update_shape
end Project.EulerGridStep.Execution
