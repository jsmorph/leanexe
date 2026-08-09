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
  unfold LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_1_singleton_wrapper_0
  apply FixedArraySingletonWrapper.wrapperProgram_spec
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
  · intro value
    change Wasm.TerminatesWith env LeanExeGen.GeneratedR1b9b2027715ddee5.«module» 0
      initial [.i64 value]
        (fun final results => final = initial ∧ results = [.i64 value])
    apply LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
    let loopInv : ScalarTransition.State → Prop := fun current =>
      ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64,
        current =
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).toState ∧
        v3 + v4 = value
    let loopMeasure : ScalarTransition.State → Nat := fun current =>
      match current.locals[2]? with
      | some (Wasm.Value.i64 remaining) => remaining.toNat
      | _ => 0
    apply ScalarTransition.postTestProgram_spec
      (condition := LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition)
      (body := LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body)
      (scratch := 12)
      (initial :=
        (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value value 0 value 0 0 0 0 0 0 0 0 0 0 0 0).toState)
      (values := [])
      (module_ := LeanExeGen.GeneratedR1b9b2027715ddee5.«module»)
      (env := env) (store := initial)
      (rest := LeanExeGen.GeneratedR1b9b2027715ddee5.func0.drop 11)
      (Inv := loopInv) (measure := loopMeasure)
    · dsimp [loopInv]
      refine ⟨value, 0, value, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, ?_⟩
      simp
    · intro current hCurrent
      dsimp [loopInv] at hCurrent
      rcases hCurrent with
        ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15,
          rfl, hSum⟩
      by_cases hRemaining : v3 = 0
      · subst v3
        have hResult : v4 = value := by simpa using hSum
        subst v4
        let afterBody :=
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 0 value 0 value v7 v8 0 value v11 1 0 value 1).toState
        refine ⟨afterBody, ?_, true, afterBody, ?_, ?_⟩
        · simpa [afterBody,
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition]
            using
              (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
                value v1 v2 0 value v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
        · simpa [afterBody,
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
            using
              (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
                value v1 v2 0 value 0 value v7 v8 0 value v11 1 0 value 1)
        · unfold LeanExeGen.GeneratedR1b9b2027715ddee5.func0
          wp_run
          simp [afterBody,
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
            ScalarTransition.U64State.toState, ScalarTransition.State.toLocals]
      · let nextRemaining := v3 - 1
        let nextResult := v4 + 1
        let afterBody :=
          (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state
            value v1 v2 nextRemaining nextResult v3 v4 nextRemaining nextResult
              nextRemaining nextResult v11 0 nextRemaining nextResult 1).toState
        refine ⟨afterBody, ?_, false, afterBody, ?_, ?_⟩
        · simpa [afterBody, nextRemaining, nextResult, hRemaining,
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
            ScalarTransition.U64Op.apply]
            using
              (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
                value v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
        · simpa [afterBody, nextRemaining, nextResult,
            LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
            using
              (LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
                value v1 v2 nextRemaining nextResult v3 v4 nextRemaining nextResult
                  nextRemaining nextResult v11 0 nextRemaining nextResult 1)
        · constructor
          · dsimp [loopInv, afterBody, nextRemaining, nextResult]
            refine ⟨v1, v2, v3 - 1, v4 + 1, v3, v4, v3 - 1, v4 + 1,
              v3 - 1, v4 + 1, v11, 0, v3 - 1, v4 + 1, 1, rfl, ?_⟩
            calc
              (v3 - 1) + (v4 + 1) = (v3 - 1) + (1 + v4) := by
                rw [UInt64.add_comm v4 1]
              _ = ((v3 - 1) + 1) + v4 := by
                rw [← UInt64.add_assoc]
              _ = v3 + v4 := by rw [UInt64.sub_add_cancel]
              _ = value := hSum
          · dsimp [loopMeasure, afterBody, nextRemaining, nextResult]
            simp [LeanExeGen.GeneratedR1b9b2027715ddee5.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
              ScalarTransition.U64State.toState]
            have hOneLe : (1 : UInt64) ≤ v3 := by
              have hPositive : (0 : UInt64) < v3 :=
                UInt64.pos_iff_ne_zero.mpr hRemaining
              rw [UInt64.le_iff_toNat_le]
              have hPositiveNat := UInt64.lt_iff_toNat_lt.mp hPositive
              simp only [UInt64.toNat_zero, UInt64.toNat_one] at hPositiveNat ⊢
              omega
            exact UInt64.lt_iff_toNat_lt.mp
              (UInt64.sub_lt UInt64.zero_lt_one hOneLe)
  · intro _
    rfl
  · intro hSize
    unfold LeanExeGen.GeneratedR1b9b2027715ddee5.FormalSpec.expected
    apply Array.ext
    · simpa [hSize]
    · intro i hInputIndex hSingletonIndex
      have hi : i = 0 := by simpa using hSingletonIndex
      subst i
      simp

end LeanExeGen.GeneratedR1b9b2027715ddee5.Behavior
