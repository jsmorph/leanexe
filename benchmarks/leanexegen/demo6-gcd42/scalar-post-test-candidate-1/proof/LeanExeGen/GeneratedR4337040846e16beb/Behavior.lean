import LeanExeGen.GeneratedR4337040846e16beb.FormalSpec
import LeanExeGen.GeneratedR4337040846e16beb.Program
import LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR4337040846e16beb.Behavior

open Wasm Project.ProofKit

private abbrev ScalarState := Project.ProofKit.ScalarTransition.State

private def gcdTransform (value : UInt64) : UInt64 :=
  UInt64.ofNat (Nat.gcd value.toNat 42)

private def gcdInv (value : UInt64) (state : ScalarState) : Prop :=
  ∃ a b v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 : UInt64,
    state =
      (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
        value value 42 a b v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18).toState ∧
    Nat.gcd a.toNat b.toNat = Nat.gcd value.toNat 42

private def gcdMeasure (state : ScalarState) : Nat :=
  match state.get 4 with
  | some (.i64 value) => value.toNat
  | _ => 0

private theorem gcd_callee (env : HostEnv Unit) (initial : Store Unit) (value : UInt64) :
    Wasm.TerminatesWith env LeanExeGen.GeneratedR4337040846e16beb.«module» 0
      initial [.i64 value]
      (fun final results =>
        final = initial ∧ results = [.i64 (gcdTransform value)]) := by
  apply
    LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
  apply Project.ProofKit.ScalarTransition.postTestProgram_spec
    (Inv := gcdInv value) (measure := gcdMeasure)
  · exact ⟨value, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, rfl⟩
  · intro current hCurrent
    rcases hCurrent with
      ⟨a, b, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16,
        v17, v18, rfl, hGcd⟩
    by_cases hb : b = 0
    · subst b
      let after :=
        (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value value 42 a 0 a 0 v7 v8 v9 a 0 v12 v13 v14 1 a 0 1).toState
      refine ⟨after, ?_, true, after, ?_, ?_⟩
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
        simp [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition]
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
        simp [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
      · have hResult : a = gcdTransform value := by
          unfold gcdTransform
          rw [← hGcd]
          simp
        simp only [if_true]
        unfold after
        unfold LeanExeGen.GeneratedR4337040846e16beb.func0
        wp_run
        simp [hResult,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          Project.ProofKit.ScalarTransition.U64State.toState,
          Project.ProofKit.ScalarTransition.State.get,
          Project.ProofKit.ScalarTransition.State.set?]
    · let remainder := a % b
      let after :=
        (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value value 42 b remainder a b remainder b remainder b remainder v12 a b 0 b remainder 1).toState
      refine ⟨after, ?_, false, after, ?_, ?_⟩
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
        simp [after, remainder,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          Project.ProofKit.ScalarTransition.U64Op.apply, hb]
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
        simp [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
      · constructor
        · refine ⟨b, remainder, a, b, remainder, b, remainder, b, remainder,
            v12, a, b, 0, b, remainder, 1, rfl, ?_⟩
          unfold remainder
          rw [UInt64.toNat_mod]
          calc
            Nat.gcd b.toNat (a.toNat % b.toNat) =
                Nat.gcd (a.toNat % b.toNat) b.toNat := Nat.gcd_comm _ _
            _ = Nat.gcd b.toNat a.toNat := (Nat.gcd_rec b.toNat a.toNat).symm
            _ = Nat.gcd a.toNat b.toNat := Nat.gcd_comm _ _
            _ = Nat.gcd value.toNat 42 := hGcd
        · have hbNat : 0 < b.toNat := by
            apply Nat.pos_of_ne_zero
            intro hZero
            apply hb
            apply UInt64.toNat.inj
            simpa using hZero
          simpa [gcdMeasure, after,
            LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.get, remainder] using
              (Nat.mod_lt a.toNat hbNat)

theorem artifact_behavior :
    LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.ArtifactSpec LeanExeGen.GeneratedR4337040846e16beb.«module» := by
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
      LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.UInt64ArrayAt st ptr values ↔
        UInt64Array.At st ptr values := by
    rfl
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedR4337040846e16beb.func1Def) rfl
  unfold LeanExeGen.GeneratedR4337040846e16beb.func1Def
  simp only [Wasm.Function.numParams, List.length, List.drop,
    Nat.zero_add, List.append_nil]
  simp only [hAtIff]
  apply Wasm.wp.conseq (Q :=
    FixedArrayPairResult.publicPost (LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected input))
  · intro continuation hPost
    cases continuation <;> simp_all [FixedArrayPairResult.publicPost]
  change wp LeanExeGen.GeneratedR4337040846e16beb.«module» LeanExeGen.GeneratedR4337040846e16beb.func1
    (FixedArrayPairResult.publicPost (LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected input))
    initial (FixedArraySingletonWrapper.entryFrame inputPtr) env
  rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_1_singleton_wrapper_0_eq]
  apply FixedArraySingletonWrapper.wrapperProgram_spec
    0 gcdTransform LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected
    LeanExeGen.GeneratedR4337040846e16beb.«module» env initial inputPtr input heapTop allocs
  · exact hArray
  · exact hOutputFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · intro value
    exact gcd_callee env initial value
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize,
      gcdTransform]

end LeanExeGen.GeneratedR4337040846e16beb.Behavior
