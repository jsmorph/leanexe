import Project.ClobLimit.LimitEntry
import Project.ProofKit.FixedArrayInMemory
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayCopy

namespace Project.ClobLimit.HeapAppendProgram
open Wasm Project.ProofKit Project.ClobLimit.LimitEntry

def headerProgram : Wasm.Program :=
  [.localGet 60, .localSet 46, .localGet 46, .wrapI64, .localGet 45, .store64 0]

def program : Wasm.Program :=
  FixedArrayCapacity.localProgram 45 5 55 ++ FixedArrayAllocate.program 55 5 ++
    headerProgram ++ FixedArrayCopy.prefixProgram 42 46 44 47 ++ residualFinishProg

set_option maxRecDepth 1048576 in
theorem residual_decomposition :
    residualProg = residualStatusProg ++ residualOrderPrepareProg ++ program := by
  rw [residualProg_decomposition]
  rfl

#print axioms residual_decomposition
end Project.ClobLimit.HeapAppendProgram
