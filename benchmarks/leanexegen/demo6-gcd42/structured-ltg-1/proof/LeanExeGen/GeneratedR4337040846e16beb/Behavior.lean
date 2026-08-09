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
      (LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
        input v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18).toState ∧
    Nat.gcd v3.toNat v4.toNat = Nat.gcd input.toNat 42

private theorem gcdCallee_spec (env : HostEnv Unit) (initial : Store Unit)
    (value : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedR4337040846e16beb.«module» 0
      initial [.i64 value]
      (fun final results =>
        final = initial ∧
          results = [.i64 (UInt64.ofNat (Nat.gcd value.toNat 42))]) := by
  apply LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_terminates_with_of_loop
  apply ScalarTransition.postTestProgram_spec
    (Inv := gcdInvariant value)
    (measure := fun current => ScalarTransition.State.localU64ToNat current 3)
  · unfold gcdInvariant
    exact ⟨value, 42, value, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      rfl, rfl⟩
  · intro current hCurrent
    rcases hCurrent with
      ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14,
        v15, v16, v17, v18, rfl, hGcd⟩
    by_cases hZero : v4 = 0
    · let after :=
        LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 v3 v4 v3 v4 v7 v8 v9 v3 v4 v12 v13 v14 1 v3 v4 1
      refine ⟨after.toState, ?_, true, after.toState, ?_, ?_⟩
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
        simp [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          hZero, after]
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
        simp [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
          after]
      · have hResult :
            v3 = UInt64.ofNat (Nat.gcd value.toNat 42) := by
          have hEncoded := congrArg UInt64.ofNat hGcd
          simpa [hZero] using hEncoded
        unfold LeanExeGen.GeneratedR4337040846e16beb.func0
        wp_run
        simp [after,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          ScalarTransition.U64State.toState, ScalarTransition.State.toLocals,
          hResult]
    · let remainder := ScalarTransition.U64Op.apply .remU v3 v4
      let after :=
        LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state
          value v1 v2 v4 remainder v3 v4 remainder v4 remainder v4 remainder v12
            v3 v4 0 v4 remainder 1
      refine ⟨after.toState, ?_, false, after.toState, ?_, ?_, ?_⟩
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_body_eval]
        simp [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_bodyTransition,
          ScalarTransition.U64Op.apply, hZero, remainder, after]
      · rw [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_condition_eval]
        simp [LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_conditionTransition,
          after]
      · unfold gcdInvariant
        refine ⟨v1, v2, v4, remainder, v3, v4, remainder, v4, remainder, v4,
          remainder, v12, v3, v4, 0, v4, remainder, 1, rfl, ?_⟩
        simp only [remainder, ScalarTransition.U64Op.apply, hZero, if_false,
          UInt64.toNat_mod]
        calc
          Nat.gcd v4.toNat (v3.toNat % v4.toNat) =
              Nat.gcd (v3.toNat % v4.toNat) v4.toNat := Nat.gcd_comm _ _
          _ = Nat.gcd v4.toNat v3.toNat := (Nat.gcd_rec v4.toNat v3.toNat).symm
          _ = Nat.gcd v3.toNat v4.toNat := Nat.gcd_comm _ _
          _ = Nat.gcd value.toNat 42 := hGcd
      · have hPositive : 0 < v4.toNat := by
          exact UInt64.lt_iff_toNat_lt.mp (UInt64.pos_iff_ne_zero.mpr hZero)
        have hDecrease := Nat.mod_lt v3.toNat hPositive
        simpa [after, remainder, ScalarTransition.State.localU64ToNat,
          ScalarTransition.U64State.toState,
          LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches.function_0_scalar_post_test_loop_0_state,
          ScalarTransition.U64Op.apply, hZero, UInt64.toNat_mod] using hDecrease

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
  refine FixedArraySingletonWrapper.wrapperProgram_spec
    (callee := 0)
    (transform := fun value => UInt64.ofNat (Nat.gcd value.toNat 42))
    (expected := LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected)
    (module_ := LeanExeGen.GeneratedR4337040846e16beb.«module»)
    (env := env) (initial := initial) (inputPtr := inputPtr) (input := input)
    (heapTop := heapTop) (allocs := allocs)
    hArray hOutputFitMemory hPages ?_ hHeapTop hFreeList hAllocs ?_ ?_ ?_
  · rfl
  · intro value
    exact gcdCallee_spec env initial value
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]
  · intro hSize
    obtain ⟨value, rfl⟩ := Array.size_eq_one_iff.mp hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected]

end LeanExeGen.GeneratedR4337040846e16beb.Behavior
