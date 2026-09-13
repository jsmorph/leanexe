import Project.EulerRiemann.Program
import Project.ProofKit.Annotation
import Project.ProofKit.ArrayFieldConstant
import Project.ProofKit.FixedArrayAllocate
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.OffsetArrayCopy

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def outputMapLoop (pressure : Bool) : Wasm.Program :=
  (Annotation.resolve func99
    [{ instructionIndex := if pressure then 99 else 47, field := .block },
      { instructionIndex := 0, field := .loop }]).getD []

def outputMapLoads (itemStart : Nat) : Wasm.Program :=
  (List.range 7).flatMap (fun field =>
    ArrayField.loadProgram 36 39 7 field ++ [.localSet (itemStart + field)])

theorem output_map_capacity_shape :
    (func99.drop 6).take 18 = FixedArrayCapacity.localProgram 37 1 42 ∧
    (func99.drop 58).take 18 = FixedArrayCapacity.localProgram 37 1 42 := by
  constructor <;> rfl

theorem output_map_allocation_shape :
    (func99.drop 24).take 15 = FixedArrayAllocate.program 42 1 ∧
    (func99.drop 76).take 15 = FixedArrayAllocate.program 42 1 := by
  constructor <;> rfl

theorem output_density_loop_shape : outputMapLoop false =
    [.localGet 39, .localGet 37, .geUI64, .br_if 1] ++ outputMapLoads 5 ++
      ArrayField.storeProgram 38 39 6 1 0 ++
      [.localGet 39, .constI64 1, .addI64, .localSet 39, .br 0] := rfl

theorem output_pressure_loop_shape : outputMapLoop true =
    [.localGet 39, .localGet 37, .geUI64, .br_if 1] ++ outputMapLoads 15 ++
      ArrayField.storeProgram 38 39 20 1 0 ++
      [.localGet 39, .constI64 1, .addI64, .localSet 39, .br 0] := rfl

theorem output_append_capacity_shape :
    (func99.drop 128).take 18 = FixedArrayCapacity.localProgram 40 1 47 ∧
    (func99.drop 304).take 18 = FixedArrayCapacity.localProgram 40 1 47 := by
  constructor <;> rfl

theorem output_append_allocation_shape :
    (func99.drop 146).take 15 = FixedArrayAllocate.program 47 1 ∧
    (func99.drop 322).take 15 = FixedArrayAllocate.program 47 1 := by
  constructor <;> rfl

theorem output_append_prefix_shape :
    (func99.drop 167).take 3 = FixedArrayCopy.prefixProgram 36 43 41 44 ∧
    (func99.drop 343).take 3 = FixedArrayCopy.prefixProgram 36 43 41 44 := by
  constructor <;> rfl

theorem output_append_suffix_shape :
    (func99.drop 170).take 3 = OffsetArrayCopy.program 37 43 42 44 none (some 41) ∧
    (func99.drop 346).take 3 = OffsetArrayCopy.program 37 43 42 44 none (some 41) := by
  constructor <;> rfl

theorem output_header_capacity_shape :
    (func99.drop 185).take 18 = FixedArrayCapacity.constantProgram 4 1 51 := rfl

theorem output_header_allocation_shape :
    (func99.drop 203).take 15 = FixedArrayAllocate.program 51 1 := rfl

theorem output_header_stores_shape : (func99.drop 224).take 56 =
    [.localGet 2, .localSet 50] ++ ArrayField.constantStoreProgram 47 0 50 1 0 ++
      [.localGet 1, .localSet 50] ++ ArrayField.constantStoreProgram 47 1 50 1 0 ++
      [.localGet 0, .localSet 50] ++ ArrayField.constantStoreProgram 47 2 50 1 0 ++
      [.localGet 0, .localSet 50] ++ ArrayField.constantStoreProgram 47 3 50 1 0 := rfl

#print axioms output_map_capacity_shape
#print axioms output_map_allocation_shape
#print axioms output_density_loop_shape
#print axioms output_pressure_loop_shape
#print axioms output_append_capacity_shape
#print axioms output_append_allocation_shape
#print axioms output_append_prefix_shape
#print axioms output_append_suffix_shape
#print axioms output_header_capacity_shape
#print axioms output_header_allocation_shape
#print axioms output_header_stores_shape

end Project.EulerRiemann.Execution
