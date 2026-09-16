import Project.TinyGpt2Infer.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayAllocate
import Project.ProofKit.ArrayPush

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.ProofKit

set_option maxRecDepth 8192

def outputBody : Wasm.Program :=
  (Annotation.resolve func75
    [{ instructionIndex := 89, field := .block },
      { instructionIndex := 0, field := .loop }]).getD []

theorem inference_loop_shape : func75 = func75.take 89 ++
    [.block 0 0 [.loop 0 0 outputBody]] ++ func75.drop 90 := rfl

theorem initial_allocation_shape : (func75.drop 52).take 15 =
    FixedArrayAllocate.program 49 1 := rfl

theorem output_allocation_shape : (outputBody.drop 67).take 15 =
    FixedArrayAllocate.program 57 1 := rfl

theorem output_copy_shape : (outputBody.drop 88).take 15 =
    FixedArrayCopy.prefixProgram 48 52 50 53 ++ UInt64Array.pushStoreProgram 52 49 54 := rfl

end Project.TinyGpt2Infer.Spec
