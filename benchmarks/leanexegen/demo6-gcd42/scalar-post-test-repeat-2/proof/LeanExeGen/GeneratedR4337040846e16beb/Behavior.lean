import LeanExeGen.GeneratedR4337040846e16beb.FormalSpec
import LeanExeGen.GeneratedR4337040846e16beb.Program
import LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR4337040846e16beb.Behavior

open Wasm Project.ProofKit

private def scalarResult (value : UInt64) : UInt64 :=
  UInt64.ofNat (Nat.gcd value.toNat 42)

private def scalarInvariant (input : UInt64)
    (current : Project.ProofKit.ScalarTransition.State) : Prop :=
  ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 : UInt64,
    current =
      (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
        input v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18).toState ∧
    Nat.gcd v3.toNat v4.toNat = Nat.gcd input.toNat 42

private def scalarMeasure
    (current : Project.ProofKit.ScalarTransition.State) : Nat :=
  match current.get 4 with
  | some (.i64 value) => value.toNat
  | _ => 0

private theorem scalar_terminates (env : HostEnv Unit) (initial : Store Unit)
    (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedR4337040846e16beb.«module» 0
      initial [.i64 value]
      (fun final results =>
        final = initial ∧ results = [.i64 (scalarResult value)]) := by
  apply LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
  apply Project.ProofKit.ScalarTransition.postTestProgram_spec
    (Inv := scalarInvariant value) (measure := scalarMeasure)
  · refine ⟨value, 42, value, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, rfl, ?_⟩
    rfl
  · intro current hCurrent
    rcases hCurrent with
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12,
        v13, v14, v15, v16, v17, v18, rfl, hGcd⟩
    by_cases hZero : v4 = 0
    · let after :=
        LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 v3 v4 v3 v4 v7 v8 v9 v3 v4 v12 v13 v14 1 v3 v4 1
      have hResult : v3 = scalarResult value := by
        apply UInt64.toNat.inj
        have hValue : v3.toNat = Nat.gcd value.toNat 42 := by
          simpa [hZero] using hGcd
        rw [hValue]
        simp [scalarResult, ← hValue]
      refine ⟨after.toState, ?_, true, after.toState, ?_, ?_⟩
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
        simp [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          hZero]
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
        simp [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
      · simp only [if_true]
        unfold LeanExeGen.GeneratedR4337040846e16beb.func0
        wp_run
        simpa [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          Project.ProofKit.ScalarTransition.U64State.toState, hResult]
    · let remainder :=
        Project.ProofKit.ScalarTransition.U64Op.apply .remU v3 v4
      let after :=
        LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 v4 remainder v3 v4 remainder v4 remainder v4 remainder
          v12 v3 v4 0 v4 remainder 1
      have hToNatNe : v4.toNat ≠ 0 := by
        intro h
        apply hZero
        apply UInt64.toNat.inj
        simpa using h
      have hPositive : 0 < v4.toNat := Nat.pos_of_ne_zero hToNatNe
      have hRemainder : remainder.toNat = v3.toNat % v4.toNat := by
        simp [remainder, Project.ProofKit.ScalarTransition.U64Op.apply, hZero]
      refine ⟨after.toState, ?_, false, after.toState, ?_, ?_⟩
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
        simp [after, remainder,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          Project.ProofKit.ScalarTransition.U64Op.apply, hZero]
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
        simp [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition]
      · constructor
        · refine ⟨v1, v2, v4, remainder, v3, v4, remainder, v4, remainder,
            v4, remainder, v12, v3, v4, 0, v4, remainder, 1, rfl, ?_⟩
          rw [hRemainder]
          calc
            Nat.gcd v4.toNat (v3.toNat % v4.toNat) =
                Nat.gcd (v3.toNat % v4.toNat) v4.toNat := Nat.gcd_comm _ _
            _ = Nat.gcd v4.toNat v3.toNat := (Nat.gcd_rec _ _).symm
            _ = Nat.gcd v3.toNat v4.toNat := Nat.gcd_comm _ _
            _ = Nat.gcd value.toNat 42 := hGcd
        · simp [scalarMeasure, after,
            LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
            Project.ProofKit.ScalarTransition.U64State.toState,
            Project.ProofKit.ScalarTransition.State.get, hRemainder]
          exact Nat.mod_lt _ hPositive

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
    0 scalarResult LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected
    LeanExeGen.GeneratedR4337040846e16beb.«module» env initial inputPtr input heapTop allocs
  · exact hArray
  · exact hOutputFitMemory
  · exact hPages
  · rfl
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · exact scalar_terminates env initial
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected,
      scalarResult, hSize]

end LeanExeGen.GeneratedR4337040846e16beb.Behavior
