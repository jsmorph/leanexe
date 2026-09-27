import Project.EulerCertificate.AnnotationMatches
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayAllocate

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit

def retryLoop : Wasm.Program :=
  match (func179[4]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def retryTrial : Wasm.Program :=
  match (retryLoop[22]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def retryFailureProgram (status : UInt64) : Wasm.Program :=
  [.constI64 status, .localSet 9, .localGet 4, .localSet 10] ++
    FixedArrayCapacity.constantProgram 0 7 123 ++ FixedArrayAllocate.program 123 7 ++
    [.localGet 128, .localSet 113, .localGet 113, .wrapI64, .constI64 0, .store64 0,
      .localGet 113, .localSet 11, .localGet 11, .localSet 12]

def retryZeroBoundary (start : Nat) : Wasm.Program :=
  [.call 67] ++
    (List.range 12).reverse.map (fun i => .localSet (start + i)) ++
    (List.range 12).flatMap (fun i => [.localGet (start + i), .localSet (13 + i)])

def retryReturn : Wasm.Program := (List.range 16).map (fun i => .localGet (9 + i))

theorem retry_loop_shape : func179 = func179.take 4 ++
    [.block 0 0 [.loop 0 0 retryLoop]] ++ func179.drop 5 := rfl

theorem retry_guard_shape : retryLoop.take 7 = FuelGuard.program 0 25 := by
  exact Option.some.inj AnnotationMatches.function_179_while_loop_0_guard_eq

theorem retry_invalid_shape : retryLoop[22]? =
    some (.iff 0 0 retryTrial
      (retryFailureProgram 3 ++ retryZeroBoundary 88 ++ [.constI64 1, .localSet 25])) := rfl

theorem retry_exhausted_shape : func179.drop 5 =
    [.localGet 25, .constI64 0, .eqI64,
      .iff 0 0 (retryFailureProgram 4 ++ retryZeroBoundary 101) []] ++ retryReturn := rfl

#print axioms retry_loop_shape
#print axioms retry_guard_shape
#print axioms retry_invalid_shape
#print axioms retry_exhausted_shape
end Project.EulerCertificate.Execution
