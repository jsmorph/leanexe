import Project.EulerRiemann.RetryLoopShape
import Project.ProofKit.FixedArrayAllocate
import Project.ProofKit.FixedArrayCapacity

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def retryFailureProgram (status : UInt64) : Wasm.Program :=
  [.constI64 status, .localSet 7, .localGet 3, .localSet 8] ++
    FixedArrayCapacity.constantProgram 0 7 51 ++ FixedArrayAllocate.program 51 7 ++
    [.localGet 56, .localSet 41, .localGet 41, .wrapI64, .constI64 0, .store64 0,
      .localGet 41, .localSet 9, .localGet 9, .localSet 10]

theorem retry_invalid_shape : retryLoop[22]? =
    some (.iff 0 0 retryTrial (retryFailureProgram 3 ++ [.constI64 1, .localSet 11])) := rfl

theorem retry_exhausted_shape : func81.drop 5 =
    [.localGet 11, .constI64 0, .eqI64, .iff 0 0 (retryFailureProgram 4) [],
      .localGet 7, .localGet 8, .localGet 9, .localGet 10] := rfl

#print axioms retry_invalid_shape
#print axioms retry_exhausted_shape

end Project.EulerRiemann.Execution
