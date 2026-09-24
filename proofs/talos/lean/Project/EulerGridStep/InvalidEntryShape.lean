import Project.EulerGridStep.InitializationShape

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow

def invalidEntryBumpBody : Wasm.Program :=
  match (gridInvalidBody[28]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

def invalidEntryAllocationRegion : Wasm.Program :=
  [.constI64 0, .localSet 48, .constI64 0, .localSet 44, .globalGet 1, .localSet 45] ++
    search 34 1 ++ [.localGet 48, .constI64 0, .eqI64, .iff 0 0 invalidEntryBumpBody []] ++
    [.globalGet 2, .constI64 1, .addI64, .globalSet 2, .localGet 48, .localSet 39]

theorem invalid_entry_capacity_shape : gridInvalidBody.take 18 =
    FixedArrayCapacity.constantProgram 1 1 43 := rfl

theorem invalid_entry_allocation_shape : (gridInvalidBody.drop 18).take 17 = invalidEntryAllocationRegion := rfl

theorem invalid_entry_bump_header_shape : invalidEntryBumpBody =
    invalidEntryBumpBody.take 28 ++ allocationHeaderProgram 48 43 := rfl

#print axioms invalid_entry_capacity_shape
#print axioms invalid_entry_allocation_shape
#print axioms invalid_entry_bump_header_shape
end Project.EulerGridStep.Execution
