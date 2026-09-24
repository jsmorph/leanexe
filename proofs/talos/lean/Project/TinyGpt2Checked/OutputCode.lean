import Project.TinyGpt2Checked.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayAllocate
import Project.ProofKit.ArrayPush
import Project.ProofKit.ArrayPushLayout
import Project.ProofKit.FixedArrayResult

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit

set_option maxRecDepth 8192

def outputBody : Wasm.Program :=
  (Annotation.resolve func84
    [{ instructionIndex := 89, field := .block },
      { instructionIndex := 0, field := .loop }]).getD []

theorem inference_loop_shape : func84 = func84.take 89 ++
    [.block 0 0 [.loop 0 0 outputBody]] ++ func84.drop 90 := rfl

theorem initial_allocation_shape : (func84.drop 52).take 15 =
    FixedArrayAllocate.program 55 1 := rfl

theorem output_allocation_shape : (outputBody.drop 69).take 15 =
    FixedArrayAllocate.program 63 1 := rfl

theorem output_copy_shape : (outputBody.drop 90).take 15 =
    FixedArrayCopy.prefixProgram 54 58 56 59 ++ UInt64Array.pushStoreProgram 58 55 60 := rfl

theorem output_prepare_shape : (outputBody.drop 69).take 21 =
    (outputBody.drop 69).take 15 ++ [.localGet 68, .localSet 58] ++
      FixedArrayResult.lengthStoreLocalProgram 58 57 := rfl

end Project.TinyGpt2Checked.Spec
