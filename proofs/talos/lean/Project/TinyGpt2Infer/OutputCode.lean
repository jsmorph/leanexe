import Project.TinyGpt2Infer.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayAllocate
import Project.ProofKit.ArrayPush
import Project.ProofKit.ArrayPushLayout
import Project.ProofKit.FixedArrayResult

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.ProofKit

set_option maxRecDepth 8192

def outputBody : Wasm.Program :=
  (Annotation.resolve func78
    [{ instructionIndex := 89, field := .block },
      { instructionIndex := 0, field := .loop }]).getD []

theorem inference_loop_shape : func78 = func78.take 89 ++
    [.block 0 0 [.loop 0 0 outputBody]] ++ func78.drop 90 := rfl

theorem initial_allocation_shape : (func78.drop 52).take 15 =
    FixedArrayAllocate.program 52 1 := rfl

theorem output_allocation_shape : (outputBody.drop 67).take 15 =
    FixedArrayAllocate.program 60 1 := rfl

theorem output_copy_shape : (outputBody.drop 88).take 15 =
    FixedArrayCopy.prefixProgram 51 55 53 56 ++ UInt64Array.pushStoreProgram 55 52 57 := rfl

theorem output_prepare_shape : (outputBody.drop 67).take 21 =
    (outputBody.drop 67).take 15 ++ [.localGet 65, .localSet 55] ++
      FixedArrayResult.lengthStoreLocalProgram 55 54 := rfl

end Project.TinyGpt2Infer.Spec
