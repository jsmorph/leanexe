import LeanExeGen.GeneratedR4337040846e16beb.FormalSpec
import LeanExeGen.GeneratedR4337040846e16beb.Program
import LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR4337040846e16beb.Behavior

open Wasm Project.ProofKit

private def scalarInvariant (input : UInt64)
    (state : ScalarTransition.State) : Prop :=
  ∃ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 : UInt64,
    state =
      (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
        input v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18).toState ∧
    Nat.gcd v3.toNat v4.toNat = Nat.gcd input.toNat 42

private def scalarMeasure (state : ScalarTransition.State) : Nat :=
  match state.get 4 with
  | some (.i64 value) => value.toNat
  | _ => 0

private theorem scalar_gcd_terminates (env : HostEnv Unit)
    (initial : Store Unit) (input : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedR4337040846e16beb.«module» 0
      initial [.i64 input]
      (fun final results =>
        final = initial ∧
          results = [.i64 (UInt64.ofNat (Nat.gcd input.toNat 42))]) := by
  apply LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
  apply ScalarTransition.postTestProgram_spec
    (Inv := scalarInvariant input) (measure := scalarMeasure)
  · exact ⟨input, 42, input, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      rfl, rfl⟩
  · intro current hCurrent
    rcases hCurrent with
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12,
        v13, v14, v15, v16, v17, v18, rfl, hGcd⟩
    by_cases hZero : v4 = 0
    · subst v4
      let after :=
        LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          input v1 v2 v3 0 v3 0 v7 v8 v9 v3 0 v12 v13 v14 1 v3 0 1
      refine ⟨after.toState, ?_, true, after.toState, ?_, ?_⟩
      · simpa [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          ScalarTransition.U64Op.apply] using
          (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
            input v1 v2 v3 0 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18)
      · simpa [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition] using
          (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
            input v1 v2 v3 0 v3 0 v7 v8 v9 v3 0 v12 v13 v14 1 v3 0 1)
      · have hValue :
            v3 = UInt64.ofNat (Nat.gcd input.toNat 42) := by
          simp at hGcd
          rw [← UInt64.ofNat_toNat (x := v3)]
          exact congrArg UInt64.ofNat hGcd
        apply
          (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_exit_wp
            (module := LeanExeGen.GeneratedR4337040846e16beb.«module»)
            (Q := _) (store := initial) (env := env)
            input v1 v2 v3 0 v3 0 v7 v8 v9 v3 0 v12 v13 v14 1 v3 0 1).2
        simp [ScalarTransition.U64State.toState,
          ScalarTransition.State.toLocals, hValue]
    · let remainder := v3 % v4
      let after :=
        LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          input v1 v2 v4 remainder v3 v4 remainder v4 remainder v4 remainder
            v12 v3 v4 0 v4 remainder 1
      refine ⟨after.toState, ?_, false, after.toState, ?_, ?_⟩
      · simpa [after, remainder,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          ScalarTransition.U64Op.apply, hZero] using
          (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval
            input v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18)
      · simpa [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition] using
          (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval
            input v1 v2 v4 remainder v3 v4 remainder v4 remainder v4 remainder
              v12 v3 v4 0 v4 remainder 1)
      · constructor
        · refine ⟨v1, v2, v4, remainder, v3, v4, remainder, v4, remainder,
            v4, remainder, v12, v3, v4, 0, v4, remainder, 1, rfl, ?_⟩
          calc
            Nat.gcd v4.toNat remainder.toNat =
                Nat.gcd v4.toNat (v3.toNat % v4.toNat) := by
                  simp [remainder, UInt64.toNat_mod]
            _ = Nat.gcd (v3.toNat % v4.toNat) v4.toNat :=
              Nat.gcd_comm _ _
            _ = Nat.gcd v4.toNat v3.toNat :=
              (Nat.gcd_rec v4.toNat v3.toNat).symm
            _ = Nat.gcd v3.toNat v4.toNat := Nat.gcd_comm _ _
            _ = Nat.gcd input.toNat 42 := hGcd
        · have hPositive : 0 < v4.toNat := by
            apply Nat.pos_of_ne_zero
            intro h
            apply hZero
            rw [← UInt64.ofNat_toNat (x := v4), h]
            rfl
          have hRemainder := Nat.mod_lt v3.toNat hPositive
          simpa [scalarMeasure, after, remainder,
            LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
            ScalarTransition.U64State.toState, ScalarTransition.State.get,
            UInt64.toNat_mod] using hRemainder

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
    exact scalar_gcd_terminates env initial value
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]

end LeanExeGen.GeneratedR4337040846e16beb.Behavior
