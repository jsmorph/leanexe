import Project.EulerRiemann.ExecutionInitialGrow
import Project.ProofKit.ConstantFieldStores
import Project.ProofKit.CheckedNatMul

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def initialCellsBody : Wasm.Program :=
  (Annotation.resolve func96 [{ instructionIndex := 4, field := .thenBranch }]).getD []

def initialSingletonFit : Wasm.Program :=
  (Annotation.resolve initialCellsBody
    [{ instructionIndex := 51, field := .block }, { instructionIndex := 0, field := .loop },
      { instructionIndex := 23, field := .thenBranch }]).getD []

theorem initial_singleton_mul_shape : (initialCellsBody.drop 8).take 4 = CheckedNatMul.program 21 22 := rfl

theorem initial_singleton_capacity_shape : (initialCellsBody.drop 27).take 18 =
    FixedArrayCapacity.constantProgram 1 7 31 := rfl

theorem initial_singleton_allocation_shape : (initialCellsBody.drop 45).take 15 =
    FixedArrayAllocateNone.program 31 initialSingletonFit 7 := rfl

theorem initial_singleton_store_shape : (initialCellsBody.drop 80).take 84 =
    ArrayField.constantStoresProgram 21 0 24 7 0 7 := rfl

#print axioms initial_singleton_mul_shape
#print axioms initial_singleton_capacity_shape
#print axioms initial_singleton_allocation_shape
#print axioms initial_singleton_store_shape

end Project.EulerRiemann.Execution
