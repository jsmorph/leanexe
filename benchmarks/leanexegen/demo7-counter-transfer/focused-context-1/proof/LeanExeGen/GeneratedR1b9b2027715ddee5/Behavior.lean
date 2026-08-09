import LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec
import LeanExeGen.GeneratedR1b9b2027715ddee5.Program
import LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior

open Wasm Project.ProofKit

private def scalarInv (value : UInt64)
    (current : ScalarTransition.State) : Prop :=
  ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64,
    current =
      (AnnotationMatches.function_0_scalar_post_test_loop_0_state
        value v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).toState ∧
    v3 + v4 = value

private def scalarMeasure (current : ScalarTransition.State) : Nat :=
  ScalarTransition.State.localU64ToNat current 2

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
    inputPtr input heapTop allocs hArray hOutputFitMemory hPages
    rfl hHeapTop hFreeList hAllocs
  · intro value
    apply AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
    apply ScalarTransition.postTestProgram_spec
      (Inv := scalarInv value) (measure := scalarMeasure)
    · exact ⟨value, 0, value, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        rfl, by simp⟩
    · intro current hCurrent
      rcases hCurrent with
        ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13,
          v14, v15, rfl, hSum⟩
      by_cases hZero : v3 = 0
      · let after :=
          AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 v3 v4 v3 v4 v7 v8 v3 v4 v11 1 v3 v4 1
        refine ⟨after.toState, ?_, true, after.toState, ?_, ?_⟩
        · rw [AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
          simp [AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            hZero, after]
        · rw [AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
          simp [AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
            after]
        · have hResult : v4 = value := by
            simpa [hZero] using hSum
          unfold LeanExeGen.GeneratedR1b9b2027715ddee5.func0
          wp_run
          simp [after, ScalarTransition.U64State.toState,
            ScalarTransition.State.toLocals,
            AnnotationMatches.function_0_scalar_post_test_loop_0_state,
            hResult]
      · let after :=
          AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 (v3 - 1) (v4 + 1) v3 v4 (v3 - 1) (v4 + 1)
              (v3 - 1) (v4 + 1) v11 0 (v3 - 1) (v4 + 1) 1
        refine ⟨after.toState, ?_, false, after.toState, ?_, ?_⟩
        · rw [AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
          simp [AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            ScalarTransition.U64Op.apply, hZero, after]
        · rw [AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
          simp [AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
            after]
        · constructor
          · refine ⟨v1, v2, v3 - 1, v4 + 1, v3, v4, v3 - 1, v4 + 1,
              v3 - 1, v4 + 1, v11, 0, v3 - 1, v4 + 1, 1, rfl, ?_⟩
            rw [ScalarTransition.CounterTransition.decrement_add_increment]
            exact hSum
          · simpa [scalarMeasure, ScalarTransition.State.localU64ToNat, after,
              AnnotationMatches.function_0_scalar_post_test_loop_0_state,
              ScalarTransition.U64State.toState] using
              ScalarTransition.CounterTransition.decrement_toNat_lt hZero
  · intro
    rfl
  · intro hSize
    apply Array.ext
    · simpa [FormalSpec.expected] using hSize
    · intro i hInputIndex hSingletonIndex
      simp at hSingletonIndex
      have hi : i = 0 := by omega
      subst i
      rfl

end LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior
