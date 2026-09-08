import Project.EulerGridStep.RejectedShape
import Project.EulerGridStep.AllocationHeader

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit.FixedArrayAllocatorWindow

def rejectedBumpBody : Wasm.Program :=
  match (rejectedCloneBody[32]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

def rejectedAllocationRegion : Wasm.Program :=
  [.constI64 0, .localSet 81, .constI64 0, .localSet 77, .globalGet 1, .localSet 78] ++
    search 67 1 ++ [.localGet 81, .constI64 0, .eqI64, .iff 0 0 rejectedBumpBody []] ++
    [.globalGet 2, .constI64 1, .addI64, .globalSet 2, .localGet 81, .localSet 71]

theorem rejected_allocation_shape : (rejectedCloneBody.drop 22).take 17 =
    rejectedAllocationRegion := rfl

theorem rejected_bump_header_shape : rejectedBumpBody =
    rejectedBumpBody.take 28 ++ allocationHeaderProgram 81 76 := rfl

theorem rejected_clone_shape : rejectedCloneBody = rejectedCloneBody.take 22 ++
    rejectedAllocationRegion ++ rejectedCloneBody.drop 39 := by
  calc
    _ = rejectedCloneBody.take 22 ++ rejectedCloneBody.drop 22 := (List.take_append_drop 22 _).symm
    _ = rejectedCloneBody.take 22 ++
        ((rejectedCloneBody.drop 22).take 17 ++ (rejectedCloneBody.drop 22).drop 17) := by
      exact congrArg (fun tail => rejectedCloneBody.take 22 ++ tail)
        (List.take_append_drop 17 (rejectedCloneBody.drop 22)).symm
    _ = _ := by rw [rejected_allocation_shape, List.drop_drop, List.append_assoc]

#print axioms rejected_allocation_shape
#print axioms rejected_bump_header_shape
#print axioms rejected_clone_shape
end Project.EulerGridStep.Execution
