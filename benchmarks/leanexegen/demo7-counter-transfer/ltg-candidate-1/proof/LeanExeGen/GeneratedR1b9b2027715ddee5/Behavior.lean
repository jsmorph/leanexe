import LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec
import LeanExeGen.GeneratedR1b9b2027715ddee5.Program
import LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior

open Wasm Project.ProofKit

private theorem scalar_identity
    (env : HostEnv Unit) (initial : Store Unit) (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedR1b9b2027715ddee5.«module» 0
      initial [.i64 value]
      (fun final results => final = initial ∧ results = [.i64 value]) := by
  apply AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
  unfold AnnotationMatches.function_0_scalar_post_test_loop_0_program
  apply ScalarTransition.postTestProgram_spec
    (Inv := fun current =>
      ∃ v1 v2 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
        current =
          (AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).toState ∧
        remaining + result = value)
    (measure := fun current => ScalarTransition.State.localU64ToNat current 2)
  · refine ⟨value, 0, value, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, ?_⟩
    simp
  · intro current hCurrent
    rcases hCurrent with
      ⟨v1, v2, remaining, result, v5, v6, v7, v8, v9, v10, v11,
        v12, v13, v14, v15, rfl, hSum⟩
    by_cases hRemaining : remaining = 0
    · subst remaining
      have hResult : result = value := by simpa using hSum
      subst result
      let after :=
        (AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 0 value 0 value v7 v8 0 value v11 1 0 value 1).toState
      refine ⟨after, ?_, true, after, ?_, ?_⟩
      · simpa [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition]
          using AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
            value v1 v2 0 value v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
      · simpa [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
          using AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
            value v1 v2 0 value 0 value v7 v8 0 value v11 1 0 value 1
      · simp only [if_true]
        change wp LeanExeGen.GeneratedR1b9b2027715ddee5.«module»
          [.localGet 4, .localSet 11, .localGet 11] _ initial
          (after.toLocals []) env
        unfold after
        wp_run
        simp [AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          ScalarTransition.U64State.toState, ScalarTransition.State.toLocals]
    · let after :=
        (AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 (remaining - 1) (result + 1) remaining result
          (remaining - 1) (result + 1) (remaining - 1) (result + 1) v11 0
          (remaining - 1) (result + 1) 1).toState
      refine ⟨after, ?_, false, after, ?_, ?_⟩
      · simpa [after, hRemaining,
          ScalarTransition.U64Op.apply,
          AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition]
          using AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
            value v1 v2 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
      · simpa [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
          using AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
            value v1 v2 (remaining - 1) (result + 1) remaining result
              (remaining - 1) (result + 1) (remaining - 1) (result + 1) v11 0
              (remaining - 1) (result + 1) 1
      · constructor
        · refine ⟨v1, v2, remaining - 1, result + 1, remaining, result,
            remaining - 1, result + 1, remaining - 1, result + 1, v11, 0,
            remaining - 1, result + 1, 1, ?_, ?_⟩
          · rfl
          · exact
              (ScalarTransition.CounterTransition.decrement_add_increment
                remaining result).trans hSum
        · simpa [after, ScalarTransition.State.localU64ToNat,
            AnnotationMatches.function_0_scalar_post_test_loop_0_state,
            ScalarTransition.U64State.toState] using
              ScalarTransition.CounterTransition.decrement_toNat_lt hRemaining

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
    (callee := 0) (transform := fun value => value)
    (expected := LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected)
    (heapTop := heapTop) (allocs := allocs)
  · exact hArray
  · exact hOutputFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · exact scalar_identity env initial
  · intro hSize
    rfl
  · intro hSize
    simp only [LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected]
    apply Array.ext
    · simpa using hSize
    · intro i hInputIndex hSingletonIndex
      have hi : i = 0 := by omega
      subst i
      rfl

end LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior
