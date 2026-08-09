import LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec
import LeanExeGen.GeneratedR1b9b2027715ddee5.Program
import LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior

open Wasm Project.ProofKit

def scalarInvariant (input : UInt64)
    (current : ScalarTransition.State) : Prop :=
  ∃ v1 v2 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
    current =
      (AnnotationMatches.function_0_scalar_post_test_loop_0_state
        input v1 v2 remaining result v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).toState ∧
    remaining + result = input

theorem scalar_terminates (env : HostEnv Unit) (initial : Store Unit)
    (input : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedR1b9b2027715ddee5.«module» 0
      initial [.i64 input]
      (fun final results => final = initial ∧ results = [.i64 input]) := by
  refine AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_post_test
    (env := env) (initial := initial)
    (P := fun final results => final = initial ∧ results = [.i64 input])
    (v0 := input) (Inv := scalarInvariant input)
    (measure := fun state => ScalarTransition.State.localU64ToNat state 2) ?_ ?_
  · refine ⟨input, 0, input, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, ?_⟩
    simp
  · intro current hCurrent
    rcases hCurrent with
      ⟨v1, v2, remaining, result, v5, v6, v7, v8, v9, v10,
        v11, v12, v13, v14, v15, rfl, hSum⟩
    by_cases hRemaining : remaining = 0
    · subst remaining
      let after :=
        (AnnotationMatches.function_0_scalar_post_test_loop_0_state
          input v1 v2 0 result 0 result v7 v8 0 result v11 1 0 result 1).toState
      refine ⟨after, ?_, true, after, ?_, ?_⟩
      · rw [AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
        simp [AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          after]
      · rw [AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
        simp [AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
          after]
      · simp only [if_true]
        have hResult : result = input := by
          simpa using hSum
        subst result
        unfold LeanExeGen.GeneratedR1b9b2027715ddee5.func0
        wp_run
        simp [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          ScalarTransition.U64State.toState, ScalarTransition.State.toLocals]
    · let after :=
        (AnnotationMatches.function_0_scalar_post_test_loop_0_state
          input v1 v2 (remaining - 1) (result + 1) remaining result
          (remaining - 1) (result + 1) (remaining - 1) (result + 1)
          v11 0 (remaining - 1) (result + 1) 1).toState
      refine ⟨after, ?_, false, after, ?_, ?_⟩
      · rw [AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
        simp [AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          ScalarTransition.U64Op.apply, hRemaining, after]
      · rw [AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
        simp [AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
          after]
      · constructor
        · refine ⟨v1, v2, remaining - 1, result + 1, remaining, result,
            remaining - 1, result + 1, remaining - 1, result + 1,
            v11, 0, remaining - 1, result + 1, 1, rfl, ?_⟩
          rw [ScalarTransition.CounterTransition.decrement_add_increment]
          exact hSum
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
    exact scalar_terminates env initial value
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
