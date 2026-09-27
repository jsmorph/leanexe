import LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec
import LeanExeGen.GeneratedRf75664d74ca656b6.Program
import LeanExeGen.GeneratedRf75664d74ca656b6.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedRf75664d74ca656b6.Behavior

open Wasm Project.ProofKit

theorem artifact_behavior :
    LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.ArtifactSpec LeanExeGen.GeneratedRf75664d74ca656b6.«module» := by
  refine ⟨1, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hOutputFit32, hOutputFitMemory,
      hHeapFit32, hHeapFitMemory, hPages⟩
  change UInt64Array.At initial inputPtr input at hArray
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  have hAtIff (st : Store Unit) (ptr : UInt64) (values : Array UInt64) :
      LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.UInt64ArrayAt st ptr values ↔
        UInt64Array.At st ptr values := by
    rfl
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRf75664d74ca656b6.func1Def) rfl
  unfold LeanExeGen.GeneratedRf75664d74ca656b6.func1Def
  simp only [Wasm.Function.numParams, List.length, List.drop,
    Nat.zero_add, List.append_nil]
  simp only [hAtIff]
  apply Wasm.wp.conseq (Q :=
    FixedArrayPairResult.publicPost (LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.expected input))
  · intro continuation hPost
    cases continuation <;> simp_all [FixedArrayPairResult.publicPost]
  change wp LeanExeGen.GeneratedRf75664d74ca656b6.«module» LeanExeGen.GeneratedRf75664d74ca656b6.func1
    (FixedArrayPairResult.publicPost (LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.expected input))
    initial (FixedArraySingletonWrapper.entryFrame inputPtr) env
  rw [LeanExeGen.GeneratedRf75664d74ca656b6.AnnotationMatches.function_1_singleton_wrapper_0_eq]
  change wp LeanExeGen.GeneratedRf75664d74ca656b6.«module»
    (FixedArraySingletonWrapper.wrapperProgram 0)
    (FixedArrayPairResult.publicPost
      (LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.expected input))
    initial (FixedArraySingletonWrapper.entryFrame inputPtr) env
  apply FixedArraySingletonWrapper.wrapperProgram_spec
    0 (fun value => value)
    LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.expected
    LeanExeGen.GeneratedRf75664d74ca656b6.«module» env initial inputPtr input
    heapTop allocs hArray hOutputFitMemory hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · intro value
    exact LeanExeGen.GeneratedRf75664d74ca656b6.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_counter_transfer_identity
      env initial value
  · intro _
    rfl
  · intro hSize
    rw [LeanExeGen.GeneratedRf75664d74ca656b6.FormalSpec.expected]
    rcases Array.size_eq_one_iff.mp hSize with ⟨value, rfl⟩
    rfl

end LeanExeGen.GeneratedRf75664d74ca656b6.Behavior
