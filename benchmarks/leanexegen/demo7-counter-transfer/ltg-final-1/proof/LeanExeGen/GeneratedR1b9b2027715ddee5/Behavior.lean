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
  have hCallee (value : UInt64) :
      Wasm.TerminatesWith env LeanExeGen.GeneratedR1b9b2027715ddee5.«module» 0
        initial [.i64 value]
        (fun final results => final = initial ∧ results = [.i64 value]) := by
    apply LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
    let Inv : ScalarTransition.State → Prop := fun current =>
      ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64,
        current =
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).toState ∧
        v3 + v4 = value
    let measure : ScalarTransition.State → Nat := fun current =>
      ScalarTransition.State.localU64ToNat current 2
    apply ScalarTransition.postTestProgram_spec
      (Inv := Inv) (measure := measure)
    · dsimp [Inv]
      refine ⟨value, 0, value, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, ?_⟩
      simp
    · intro current hCurrent
      rcases hCurrent with
        ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13,
          v14, v15, rfl, hSum⟩
      by_cases hZero : v3 = 0
      · subst v3
        have hResult : v4 = value := by simpa using hSum
        subst v4
        let after :=
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 0 value 0 value v7 v8 0 value v11 1 0 value 1).toState
        refine ⟨after, ?_, true, after, ?_, ?_⟩
        · rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
          simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            after]
        · rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
          simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
            after]
        · simp only [if_true]
          unfold LeanExeGen.GeneratedR1b9b2027715ddee5.func0
          wp_run
          simp [after,
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
            ScalarTransition.U64State.toState, ScalarTransition.State.toLocals]
      · let remaining' := ScalarTransition.U64Op.apply .sub v3 1
        let result' := ScalarTransition.U64Op.apply .add v4 1
        let after :=
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 remaining' result' v3 v4 remaining' result'
              remaining' result' v11 0 remaining' result' 1).toState
        refine ⟨after, ?_, false, after, ?_, ?_⟩
        · rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
          simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            hZero, remaining', result', after]
        · rw [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
          simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
            after]
        · constructor
          · dsimp [Inv]
            refine ⟨v1, v2, remaining', result', v3, v4, remaining', result',
              remaining', result', v11, 0, remaining', result', 1, rfl, ?_⟩
            simpa [remaining', result', ScalarTransition.U64Op.apply] using
              (ScalarTransition.CounterTransition.decrement_add_increment v3 v4).trans hSum
          · simpa [measure, after, remaining',
              LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
              ScalarTransition.U64State.toState,
              ScalarTransition.State.localU64ToNat,
              ScalarTransition.U64Op.apply] using
              ScalarTransition.CounterTransition.decrement_toNat_lt hZero
  apply FixedArraySingletonWrapper.wrapperProgram_spec
    0 (fun value => value)
    LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected
    LeanExeGen.GeneratedR1b9b2027715ddee5.«module» env initial inputPtr input
    heapTop allocs hArray hOutputFitMemory hPages rfl hHeapTop hFreeList hAllocs
    hCallee
  · intro _
    rfl
  · intro hSize
    rcases Array.size_eq_one_iff.mp hSize with ⟨value, rfl⟩
    rfl

end LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior
