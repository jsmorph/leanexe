import Project.EulerGridStep.AllocationHeader

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit.FixedArrayAllocatorWindow

def gridInvalidBody : Wasm.Program :=
  match (func36[17]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

def gridValidBody : Wasm.Program :=
  match (func36[17]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ _ body _ _) => body
  | _ => []

def initialBumpBody : Wasm.Program :=
  match (gridValidBody[64]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

def initialAllocationRegion : Wasm.Program :=
  [.constI64 0, .localSet 44, .constI64 0, .localSet 40, .globalGet 1, .localSet 41] ++
    search 30 1 ++ [.localGet 44, .constI64 0, .eqI64, .iff 0 0 initialBumpBody []] ++
    [.globalGet 2, .constI64 1, .addI64, .globalSet 2, .localGet 44, .localSet 34]

def initialZeroBody : Wasm.Program :=
  [.localGet 35, .localGet 33, .geUI64, .br_if 1,
    .localGet 34, .localGet 35, .constI64 1, .mulI64, .constI64 1, .addI64,
    .constI64 8, .mulI64, .addI64, .wrapI64, .localGet 36, .store64 0,
    .localGet 35, .constI64 1, .addI64, .localSet 35, .br 0]

def initialZeroLoop : Wasm.Program := [.block 0 0 [.loop 0 0 initialZeroBody]]

theorem grid_function_shape : func36 = func36.take 17 ++
    [.iff 0 0 gridInvalidBody gridValidBody, .localGet 32] := rfl

theorem initial_allocation_shape : (gridValidBody.drop 54).take 17 = initialAllocationRegion := rfl

theorem initial_bump_header_shape : initialBumpBody =
    initialBumpBody.take 28 ++ allocationHeaderProgram 44 39 := rfl

theorem initial_zero_shape : (gridValidBody.drop 71).take 7 =
    [.localGet 34, .wrapI64, .localGet 33, .store64 0, .constI64 0, .localSet 35] ++ initialZeroLoop := rfl

theorem grid_frame_shape : func36Def.params.length = 2 ∧ func36Def.locals.length = 43 := ⟨rfl, rfl⟩

#print axioms grid_function_shape
#print axioms initial_allocation_shape
#print axioms initial_bump_header_shape
#print axioms initial_zero_shape
#print axioms grid_frame_shape
end Project.EulerGridStep.Execution
