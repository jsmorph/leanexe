import LeanExeGen.GeneratedR4337040846e16beb.FormalSpec
import LeanExeGen.GeneratedR4337040846e16beb.Program
import LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR4337040846e16beb.Behavior

open Wasm Project.ProofKit

private def gcdInvariant (input : UInt64)
    (current : ScalarTransition.State) : Prop :=
  ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 : UInt64,
    current =
      (AnnotationMatches.function_0_scalar_post_test_loop_0_state
        input v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18).toState ∧
    Nat.gcd v3.toNat v4.toNat = Nat.gcd input.toNat 42

private def gcdMeasure (current : ScalarTransition.State) : Nat :=
  match current.locals[3]? with
  | some (Wasm.Value.i64 value) => value.toNat
  | _ => 0

private theorem gcdWith42_terminates
    (env : HostEnv Unit) (initial : Store Unit) (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedR4337040846e16beb.«module» 0
      initial [.i64 value]
      (fun final results =>
        final = initial ∧
          results = [.i64 (UInt64.ofNat (Nat.gcd value.toNat 42))]) := by
  apply AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
  apply ScalarTransition.postTestProgram_spec
    (Inv := gcdInvariant value) (measure := gcdMeasure)
  · refine ⟨value, 42, value, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, rfl⟩
  · intro current hCurrent
    rcases hCurrent with
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13,
        v14, v15, v16, v17, v18, rfl, hGcd⟩
    by_cases hZero : (v4 == 0) = true
    · have hv4 : v4 = 0 := by simpa using hZero
      subst v4
      let after :=
        (AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 v3 0 v3 0 v7 v8 v9 v3 0 v12 v13 v14 1 v3 0 1).toState
      refine ⟨after, ?_, true, after, ?_, ?_⟩
      · simpa [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition]
          using
            AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
              value v1 v2 v3 0 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
      · simpa [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
          using
            AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
              value v1 v2 v3 0 v3 0 v7 v8 v9 v3 0 v12 v13 v14 1 v3 0 1
      · have hResultNat : v3.toNat = Nat.gcd value.toNat 42 := by
          simpa using hGcd
        have hResult : v3 = UInt64.ofNat (Nat.gcd value.toNat 42) := by
          calc
            v3 = UInt64.ofNat v3.toNat := UInt64.ofNat_toNat.symm
            _ = UInt64.ofNat (Nat.gcd value.toNat 42) :=
              congrArg UInt64.ofNat hResultNat
        unfold LeanExeGen.GeneratedR4337040846e16beb.func0
        wp_run
        simpa [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          ScalarTransition.U64State.toState, ScalarTransition.State.toLocals,
          hResult]
    · have hv4 : v4 ≠ 0 := by
        intro h
        subst v4
        simp at hZero
      let remainder : UInt64 :=
        ScalarTransition.U64Op.apply .remU v3 v4
      have hRemainder : remainder = v3 % v4 := by
        simp [remainder, ScalarTransition.U64Op.apply, hv4]
      have hv4Nat : 0 < v4.toNat := by
        apply Nat.pos_of_ne_zero
        intro h
        apply hv4
        apply UInt64.toNat_inj.mp
        simpa using h
      have hDecrease : remainder.toNat < v4.toNat := by
        rw [hRemainder, UInt64.toNat_mod]
        exact Nat.mod_lt _ hv4Nat
      have hGcdNext :
          Nat.gcd v4.toNat remainder.toNat = Nat.gcd value.toNat 42 := by
        rw [hRemainder, UInt64.toNat_mod]
        calc
          Nat.gcd v4.toNat (v3.toNat % v4.toNat) =
              Nat.gcd (v3.toNat % v4.toNat) v4.toNat :=
            Nat.gcd_comm _ _
          _ = Nat.gcd v4.toNat v3.toNat :=
            (Nat.gcd_rec v4.toNat v3.toNat).symm
          _ = Nat.gcd v3.toNat v4.toNat := Nat.gcd_comm _ _
          _ = Nat.gcd value.toNat 42 := hGcd
      let after :=
        (AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 v4 remainder v3 v4 remainder v4 remainder v4 remainder
          v12 v3 v4 0 v4 remainder 1).toState
      refine ⟨after, ?_, false, after, ?_, ?_, ?_⟩
      · simpa [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          hZero]
          using
            AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
              value v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18
      · simpa [after,
          AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
          using
            AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
              value v1 v2 v4 remainder v3 v4 remainder v4 remainder v4 remainder
              v12 v3 v4 0 v4 remainder 1
      · exact ⟨v1, v2, v4, remainder, v3, v4, remainder, v4, remainder,
          v4, remainder, v12, v3, v4, 0, v4, remainder, 1, rfl, hGcdNext⟩
      · simpa [gcdMeasure, after,
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
  apply FixedArraySingletonWrapper.wrapperProgram_spec
    0 (fun value => UInt64.ofNat (Nat.gcd value.toNat 42))
    LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected
    LeanExeGen.GeneratedR4337040846e16beb.«module» env initial inputPtr input
    heapTop allocs hArray hOutputFitMemory hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · intro value
    exact gcdWith42_terminates env initial value
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]

end LeanExeGen.GeneratedR4337040846e16beb.Behavior
