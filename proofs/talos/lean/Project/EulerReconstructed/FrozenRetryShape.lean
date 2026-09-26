import Project.EulerReconstructed.FrozenAnnotationMatches
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayAllocate

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.ProofKit

def retryLoop : Wasm.Program :=
  match (func125[4]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def retryTrial : Wasm.Program :=
  match (retryLoop[22]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def retryFailureProgram (status : UInt64) : Wasm.Program :=
  [.constI64 status, .localSet 9, .localGet 4, .localSet 10] ++
    FixedArrayCapacity.constantProgram 0 7 79 ++ FixedArrayAllocate.program 79 7 ++
    [.localGet 84, .localSet 69, .localGet 69, .wrapI64, .constI64 0, .store64 0,
      .localGet 69, .localSet 11, .localGet 11, .localSet 12]

theorem retry_loop_shape : func125 = func125.take 4 ++
    [.block 0 0 [.loop 0 0 retryLoop]] ++ func125.drop 5 := rfl

theorem retry_guard_shape : retryLoop.take 7 = FuelGuard.program 0 13 := by
  have h := AnnotationMatches.function_125_while_loop_0_guard_eq
  exact Option.some.inj h

theorem retry_invalid_shape : retryLoop[22]? =
    some (.iff 0 0 retryTrial (retryFailureProgram 3 ++ [.constI64 1, .localSet 13])) := rfl

theorem retry_exhausted_shape : func125.drop 5 =
    [.localGet 13, .constI64 0, .eqI64, .iff 0 0 (retryFailureProgram 4) [],
      .localGet 9, .localGet 10, .localGet 11, .localGet 12] := rfl

#print axioms retry_loop_shape
#print axioms retry_guard_shape
#print axioms retry_invalid_shape
#print axioms retry_exhausted_shape
end Project.EulerReconstructed.Frozen.Execution
