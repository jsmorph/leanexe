import LeanExeGen.GeneratedR4337040846e16beb.FormalSpec
import LeanExeGen.GeneratedR4337040846e16beb.Program
import LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR4337040846e16beb.Behavior

open Wasm Project.ProofKit

private def gcdInv (value : UInt64)
    (current : ScalarTransition.State) : Prop :=
  ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 : UInt64,
    current =
      (AnnotationMatches.function_0_scalar_post_test_loop_0_state
        value v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18).toState ∧
    Nat.gcd v3.toNat v4.toNat = Nat.gcd value.toNat 42

private theorem scalar_spec (env : HostEnv Unit) (initial : Store Unit)
    (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedR4337040846e16beb.«module» 0
      initial [.i64 value]
      (fun final results =>
        final = initial ∧
          results = [.i64 (UInt64.ofNat (Nat.gcd value.toNat 42))]) := by
  apply AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
  apply ScalarTransition.postTestProgram_spec
    (Inv := gcdInv value)
    (measure := fun current => ScalarTransition.State.localU64ToNat current 3)
  · exact ⟨value, 42, value, 42,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, rfl⟩
  · intro current hCurrent
    rcases hCurrent with
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12,
        v13, v14, v15, v16, v17, v18, rfl, hGcd⟩
    by_cases hZero : v4 = 0
    · let afterZero :=
        AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 v3 v4 v3 v4 v7 v8 v9 v3 v4 v12 v13 v14 1 v3 v4 1
      refine ⟨afterZero.toState, ?_, true, afterZero.toState, ?_, ?_⟩
      · simpa [afterZero,
          AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          hZero] using
          (AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
            value v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18)
      · simpa [afterZero,
          AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition] using
          (AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
            value v1 v2 v3 v4 v3 v4 v7 v8 v9 v3 v4 v12 v13 v14 1 v3 v4 1)
      · have hGcd' : v3.toNat = Nat.gcd value.toNat 42 := by
          simpa [hZero] using hGcd
        have hResult : v3 = UInt64.ofNat (Nat.gcd value.toNat 42) := by
          rw [← hGcd']
          simp
        dsimp [afterZero,
          AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          ScalarTransition.U64State.toState, ScalarTransition.State.toLocals]
        unfold LeanExeGen.GeneratedR4337040846e16beb.func0
        wp_run
        simp [hResult]
    · let afterNext :=
        AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 v4 (v3 % v4) v3 v4 (v3 % v4) v4 (v3 % v4)
          v4 (v3 % v4) v12 v3 v4 0 v4 (v3 % v4) 1
      have hGcdNext :
          Nat.gcd v4.toNat (v3 % v4).toNat = Nat.gcd value.toNat 42 := by
        rw [UInt64.toNat_mod]
        calc
          Nat.gcd v4.toNat (v3.toNat % v4.toNat) =
              Nat.gcd (v3.toNat % v4.toNat) v4.toNat := Nat.gcd_comm _ _
          _ = Nat.gcd v4.toNat v3.toNat := (Nat.gcd_rec _ _).symm
          _ = Nat.gcd v3.toNat v4.toNat := Nat.gcd_comm _ _
          _ = Nat.gcd value.toNat 42 := hGcd
      have hPositive : 0 < v4.toNat := by
        have hPositiveU64 : (0 : UInt64) < v4 :=
          UInt64.pos_iff_ne_zero.mpr hZero
        simpa using UInt64.lt_iff_toNat_lt.mp hPositiveU64
      have hDecrease : (v3 % v4).toNat < v4.toNat := by
        rw [UInt64.toNat_mod]
        exact Nat.mod_lt _ hPositive
      refine ⟨afterNext.toState, ?_, false, afterNext.toState, ?_, ?_, ?_⟩
      · simpa [afterNext,
          AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          ScalarTransition.U64Op.apply, hZero] using
          (AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
            value v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18)
      · simpa [afterNext,
          AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition] using
          (AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
            value v1 v2 v4 (v3 % v4) v3 v4 (v3 % v4) v4 (v3 % v4)
              v4 (v3 % v4) v12 v3 v4 0 v4 (v3 % v4) 1)
      · exact ⟨v1, v2, v4, v3 % v4, v3, v4, v3 % v4, v4,
          v3 % v4, v4, v3 % v4, v12, v3, v4, 0, v4, v3 % v4, 1,
          rfl, hGcdNext⟩
      · simpa [afterNext, ScalarTransition.State.localU64ToNat,
          AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          ScalarTransition.U64State.toState] using hDecrease

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
  unfold LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_1_singleton_wrapper_0
  apply FixedArraySingletonWrapper.wrapperProgram_spec
    (transform := fun value => UInt64.ofNat (Nat.gcd value.toNat 42))
    (heapTop := heapTop) (allocs := allocs)
  · exact hArray
  · exact hOutputFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · intro value
    exact scalar_spec env initial value
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]
  · intro hSize
    obtain ⟨value, rfl⟩ := Array.size_eq_one_iff.mp hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected]

end LeanExeGen.GeneratedR4337040846e16beb.Behavior
