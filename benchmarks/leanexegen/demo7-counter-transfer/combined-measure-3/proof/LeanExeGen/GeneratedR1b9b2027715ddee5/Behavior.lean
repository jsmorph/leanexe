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
  have hCallee : ∀ value : UInt64,
      Wasm.TerminatesWith env LeanExeGen.GeneratedR1b9b2027715ddee5.«module» 0
        initial [.i64 value]
        (fun final results => final = initial ∧ results = [.i64 value]) := by
    intro value
    apply LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
    let loopInv : Project.ProofKit.ScalarTransition.State → Prop := fun current =>
      ∃ v1 v2 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
        current =
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).toState ∧
        remaining + result = value
    apply Project.ProofKit.ScalarTransition.postTestProgram_spec
      (Inv := loopInv)
      (measure := fun current =>
        Project.ProofKit.ScalarTransition.State.combinedLocalU64ToNat current 3)
    · refine ⟨value, 0, value, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, ?_⟩
      simp
    · intro current hCurrent
      rcases hCurrent with
        ⟨v1, v2, remaining, result, v5, v6, v7, v8, v9, v10, v11,
          v12, v13, v14, v15, rfl, hSum⟩
      by_cases hRemaining : remaining = 0
      · let after :=
          LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 remaining result remaining result v7 v8 remaining result v11
              1 remaining result 1
        refine ⟨after.toState, ?_, true, after.toState, ?_, ?_⟩
        · rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
          simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            hRemaining, after]
        · rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
          simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
            after]
        · have hResult : result = value := by
            simpa [hRemaining] using hSum
          subst result
          subst remaining
          unfold LeanExeGen.GeneratedR1b9b2027715ddee5.func0
          wp_run
          simp [after,
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.toLocals]
      · let nextRemaining := remaining - 1
        let nextResult := result + 1
        let after :=
          LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 nextRemaining nextResult remaining result nextRemaining nextResult
              nextRemaining nextResult v11 0 nextRemaining nextResult 1
        refine ⟨after.toState, ?_, false, after.toState, ?_, ?_⟩
        · rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
          simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            Project.ProofKit.ScalarTransition.U64Op.apply, hRemaining,
            nextRemaining, nextResult, after]
        · rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
          simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
            after]
        · constructor
          · refine ⟨v1, v2, nextRemaining, nextResult, remaining, result,
              nextRemaining, nextResult, nextRemaining, nextResult, v11, 0,
              nextRemaining, nextResult, 1, rfl, ?_⟩
            rw [Project.ProofKit.ScalarTransition.CounterTransition.decrement_add_increment]
            exact hSum
          · simpa [after, nextRemaining,
              Project.ProofKit.ScalarTransition.State.combinedLocalU64ToNat,
              LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
              Project.ProofKit.ScalarTransition.U64State.toState,
              Project.ProofKit.ScalarTransition.State.get] using
                (Project.ProofKit.ScalarTransition.CounterTransition.decrement_toNat_lt hRemaining)
  apply Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram_spec
    (callee := 0) (transform := id)
    (expected := LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected)
    (module_ := LeanExeGen.GeneratedR1b9b2027715ddee5.«module»)
    (env := env) (initial := initial) (inputPtr := inputPtr) (input := input)
    (heapTop := heapTop) (allocs := allocs)
  · exact hArray
  · exact hOutputFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · simpa using hCallee
  · intro _
    rfl
  · intro hSize
    unfold LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected
    apply Array.ext
    · simpa using hSize
    · intro i hInputIndex hSingletonIndex
      have hi : i = 0 := by omega
      subst i
      simp

end LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior
