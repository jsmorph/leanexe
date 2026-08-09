import LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec
import LeanExeGen.GeneratedR1b9b2027715ddee5.Program
import LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior

open Wasm Project.ProofKit

theorem artifact_behavior :
    LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.ArtifactSpec LeanExeGen.GeneratedR1b9b2027715ddee5.«module» := by
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
      LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.UInt64ArrayAt st ptr values ↔
        UInt64Array.At st ptr values := by
    rfl
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedR1b9b2027715ddee5.func1Def) rfl
  unfold LeanExeGen.GeneratedR1b9b2027715ddee5.func1Def
  simp only [Wasm.Function.numParams, List.length, List.drop,
    Nat.zero_add, List.append_nil]
  simp only [hAtIff]
  apply Wasm.wp.conseq (Q :=
    FixedArrayPairResult.publicPost (LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected input))
  · intro continuation hPost
    cases continuation <;> simp_all [FixedArrayPairResult.publicPost]
  change wp LeanExeGen.GeneratedR1b9b2027715ddee5.«module» LeanExeGen.GeneratedR1b9b2027715ddee5.func1
    (FixedArrayPairResult.publicPost (LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected input))
    initial (FixedArraySingletonWrapper.entryFrame inputPtr) env
  rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_1_singleton_wrapper_0_eq]
  apply FixedArraySingletonWrapper.wrapperProgram_spec
    0 (fun value => value)
    LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected
    LeanExeGen.GeneratedR1b9b2027715ddee5.«module» env initial
    inputPtr input heapTop allocs
  · exact hArray
  · exact hOutputFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · intro value
    exact LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_counter_transfer_identity
      env initial value
  · intro _
    rfl
  · intro hSize
    unfold LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected
    apply Array.ext
    · simpa using hSize
    · intro i hiInput _
      have hi : i = 0 := by omega
      subst i
      rfl

end LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior
