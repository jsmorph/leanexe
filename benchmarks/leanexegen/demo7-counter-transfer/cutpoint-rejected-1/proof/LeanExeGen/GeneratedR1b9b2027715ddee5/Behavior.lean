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
  let scalarExpected : UInt64 → UInt64 := fun value =>
    (LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected #[value])[0]!
  apply FixedArraySingletonWrapper.wrapperProgram_spec
    _ scalarExpected LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected
    LeanExeGen.GeneratedR1b9b2027715ddee5.«module» env initial inputPtr input heapTop allocs
  · exact hArray
  · exact hOutputFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · intro value
    apply LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
    let scalarInv : Project.ProofKit.ScalarTransition.State → Prop := fun state =>
      ∃ remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64,
        state =
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value value 0 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).toState ∧
        remaining + result = value
    let scalarMeasure : Project.ProofKit.ScalarTransition.State → Nat := fun state =>
      Project.ProofKit.ScalarTransition.State.localU64ToNat state 2
    apply Project.ProofKit.ScalarTransition.postTestProgram_spec
      (Inv := scalarInv) (measure := scalarMeasure)
    · refine ⟨value, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, ?_⟩
      simp
    · intro current hCurrent
      rcases hCurrent with
        ⟨remaining, result, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14,
          v15, rfl, hSum⟩
      by_cases hRemaining : remaining = 0
      · subst remaining
        have hResultValue : result = value := by
          simpa using hSum
        refine ⟨
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value value 0 0 result 0 result v7 v8 0 result v11 1 0 result 1).toState,
          ?_, ?_⟩
        · simpa [
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            Project.ProofKit.ScalarTransition.U64Op.apply] using
            (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
              value value 0 0 result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
        · refine ⟨true,
            (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
              value value 0 0 result 0 result v7 v8 0 result v11 1 0 result 1).toState,
            ?_, ?_⟩
          · simpa [
              LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition] using
              (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
                value value 0 0 result 0 result v7 v8 0 result v11 1 0 result 1)
          · simp only [if_true]
            unfold LeanExeGen.GeneratedR1b9b2027715ddee5.func0
            wp_run
            simp [
              LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
              Project.ProofKit.ScalarTransition.U64State.toState,
              Project.ProofKit.ScalarTransition.State.toLocals,
              scalarExpected,
              LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected,
              hResultValue]
      · refine ⟨
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value value 0 (remaining - 1) (result + 1) remaining result
              (remaining - 1) (result + 1) (remaining - 1) (result + 1)
              v11 0 (remaining - 1) (result + 1) 1).toState,
          ?_, ?_⟩
        · simpa [
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            Project.ProofKit.ScalarTransition.U64Op.apply, hRemaining] using
            (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
              value value 0 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
        · refine ⟨false,
            (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
              value value 0 (remaining - 1) (result + 1) remaining result
                (remaining - 1) (result + 1) (remaining - 1) (result + 1)
                v11 0 (remaining - 1) (result + 1) 1).toState,
            ?_, ?_⟩
          · simpa [
              LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition] using
              (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
                value value 0 (remaining - 1) (result + 1) remaining result
                  (remaining - 1) (result + 1) (remaining - 1) (result + 1)
                  v11 0 (remaining - 1) (result + 1) 1)
          · constructor
            · refine ⟨remaining - 1, result + 1, remaining, result,
                remaining - 1, result + 1, remaining - 1, result + 1, v11, 0,
                remaining - 1, result + 1, 1, rfl, ?_⟩
              exact
                (Project.ProofKit.ScalarTransition.CounterTransition.decrement_add_increment
                  remaining result).trans hSum
            · simpa [scalarMeasure,
                Project.ProofKit.ScalarTransition.State.localU64ToNat,
                LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
                Project.ProofKit.ScalarTransition.U64State.toState] using
                (Project.ProofKit.ScalarTransition.CounterTransition.decrement_toNat_lt
                  hRemaining)
  · intro hSize
    rfl
  · intro hSize
    simp only [LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected]
    change input = #[input[0]]
    apply Array.ext
    · simpa
    · intro i hInputIndex hSingletonIndex
      have hi : i = 0 := by omega
      subst i
      simp

end LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior
