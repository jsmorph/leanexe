import LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec
import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
import Project.ProofKit.Array
import Project.ProofKit.Control
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedArrayEqNode
import Project.ProofKit.FixedArrayFold
import Project.ProofKit.FixedArrayFoldBody
import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayAllocatorWindow
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArrayResult
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.Frame
import Project.ProofKit.ScalarTransition

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior

open Wasm Project.ProofKit

def foldLoopProgram : Wasm.Program :=
  [.block 0 0 [.loop 0 0
    (AnnotationMatches.function_0_array_fold_0_continuing_program ++
      AnnotationMatches.function_0_array_fold_0_step_program)]]

theorem validBranch_decomposition :
    AnnotationMatches.function_0_length_dispatch_0_valid_branch_program =
      FixedArrayCapacity.constantProgram 1 1 11 ++
      (FixedArrayAllocatorWindow.region 2 1 ++
      (FixedArrayResult.lengthStoreProgram 7 1 ++
      (AnnotationMatches.function_0_array_fold_0_setup_program ++
      (foldLoopProgram ++
        AnnotationMatches.function_0_array_fold_0_singleton_result_program)))) := by
  rfl

theorem invalidBranch_decomposition :
    AnnotationMatches.function_0_length_dispatch_0_invalid_branch_program =
      FixedArrayCapacity.constantProgram 0 1 11 ++
      (FixedArrayAllocatorWindow.region 2 1 ++
      (FixedArrayResult.lengthStoreProgram 7 0 ++
        FixedArrayResult.finishProgram 7 5 6)) := by
  rfl

theorem artifact_behavior :
    LeanExeGen.GeneratedR23fa7efc3fb0298b.FormalSpec.ArtifactSpec LeanExeGen.GeneratedR23fa7efc3fb0298b.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hOutputFit32, hOutputFitMemory,
      hHeapFit32, hHeapFitMemory, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.generatedLengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedR23fa7efc3fb0298b.func0Def) rfl
  wp_fixed_array_length_le_dispatch_from hArray at 7, 8
  · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · norm_num
  · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.ValueType.zero]
  · norm_num [UInt64.size]
  · intro hSize
    change Wasm.wp _
      AnnotationMatches.function_0_length_dispatch_0_valid_branch_program
      _ _ _ _
    rw [validBranch_decomposition]
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame,
        Wasm.Locals.validIndex]
  · intro hSize
    change Wasm.wp _
      AnnotationMatches.function_0_length_dispatch_0_invalid_branch_program
      _ _ _ _
    rw [invalidBranch_decomposition]
    apply FixedArrayCapacity.constantProgram_spec
    · rfl
    · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame]
    · norm_num [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams,
        Wasm.ValueType.zero, FixedArrayLengthDispatch.branchFrame,
        Wasm.Locals.validIndex]

end LeanExeGen.GeneratedR23fa7efc3fb0298b.Behavior
