import LeanExeGen.GeneratedR4337040846e16beb.FormalSpec
import LeanExeGen.GeneratedR4337040846e16beb.Program
import LeanExeGen.GeneratedR4337040846e16beb.AnnotationMatches
import Project.ProofKit.Control
import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedR4337040846e16beb.Behavior

open Wasm Project.ProofKit

structure ScalarScratch where
  v5 : UInt64
  v6 : UInt64
  v7 : UInt64
  v8 : UInt64
  v9 : UInt64
  v10 : UInt64
  v11 : UInt64
  v12 : UInt64
  v13 : UInt64
  v14 : UInt64
  v15 : UInt64
  v16 : UInt64
  v17 : UInt64
  v18 : UInt64

def zeroScratch : ScalarScratch :=
  { v5 := 0, v6 := 0, v7 := 0, v8 := 0, v9 := 0, v10 := 0, v11 := 0,
    v12 := 0, v13 := 0, v14 := 0, v15 := 0, v16 := 0, v17 := 0, v18 := 0 }

def scalarFrame (input a b : UInt64) (scratch : ScalarScratch) : Locals :=
  { params := [.i64 input]
    locals := [
      .i64 input, .i64 42, .i64 a, .i64 b,
      .i64 scratch.v5, .i64 scratch.v6, .i64 scratch.v7,
      .i64 scratch.v8, .i64 scratch.v9, .i64 scratch.v10,
      .i64 scratch.v11, .i64 scratch.v12, .i64 scratch.v13,
      .i64 scratch.v14, .i64 scratch.v15, .i64 scratch.v16,
      .i64 scratch.v17, .i64 scratch.v18]
    values := [] }

def scalarInv (initial : Store Unit) (input : UInt64) : AssertionF Unit :=
  fun st frame => ∃ a b scratch,
    st = initial ∧
    frame = scalarFrame input a b scratch ∧
    Nat.gcd a.toNat b.toNat = Nat.gcd input.toNat 42

def scalarMeasure (frame : Locals) : Nat :=
  match frame.get 4 with
  | some (.i64 b) => b.toNat
  | _ => 0

theorem scalar_correct (env : HostEnv Unit) (initial : Store Unit) (input : UInt64) :
    TerminatesWith env LeanExeGen.GeneratedR4337040846e16beb.«module» 0
      initial [.i64 input]
      (fun final results =>
        final = initial ∧
        results = [.i64 (UInt64.ofNat (Nat.gcd input.toNat 42))]) := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedR4337040846e16beb.func0Def) rfl
  unfold LeanExeGen.GeneratedR4337040846e16beb.func0Def
  simp only [Wasm.Function.numParams, List.length, List.drop,
    Nat.zero_add, List.append_nil]
  unfold LeanExeGen.GeneratedR4337040846e16beb.func0
  wp_run
  change wp _ (.block 0 0 _ :: _) _ initial
    (scalarFrame input input 42 zeroScratch) env
  apply Wasm.wp_block_cons
  apply Wasm.wp_loop_cons
    (Inv := scalarInv initial input)
    (μ := fun _ frame => scalarMeasure frame)
  · exact ⟨input, 42, zeroScratch, rfl, rfl, rfl⟩
  · intro st frame hInv
    rcases hInv with ⟨a, b, scratch, rfl, rfl, hGcd⟩
    rcases scratch with
      ⟨v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18⟩
    by_cases hb : b = 0
    · subst b
      simp [scalarFrame]
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      have hResult := congrArg UInt64.ofNat hGcd
      simpa using hResult
    · simp [scalarFrame, hb]
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp [hb]
      apply Wasm.wp_iff_cons rfl
      simp [hb]
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      apply Wasm.wp_iff_cons rfl
      simp
      constructor
      · unfold scalarInv
        refine ⟨b, a % b,
          { v5 := a, v6 := b, v7 := a % b, v8 := b, v9 := a % b,
            v10 := b, v11 := a % b, v12 := v12, v13 := a, v14 := b,
            v15 := 0, v16 := b, v17 := a % b, v18 := 1 }, rfl, rfl, ?_⟩
        rw [UInt64.toNat_mod]
        calc
          Nat.gcd b.toNat (a.toNat % b.toNat) =
              Nat.gcd (a.toNat % b.toNat) b.toNat := Nat.gcd_comm _ _
          _ = Nat.gcd b.toNat a.toNat := (Nat.gcd_rec b.toNat a.toNat).symm
          _ = Nat.gcd a.toNat b.toNat := Nat.gcd_comm _ _
          _ = Nat.gcd input.toNat 42 := hGcd
      · have hbNat : b.toNat ≠ 0 := by
          intro h
          apply hb
          apply UInt64.toNat_inj.mp
          simpa using h
        simpa [scalarMeasure, UInt64.toNat_mod] using
          Nat.mod_lt a.toNat (Nat.pos_of_ne_zero hbNat)

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
    (callee := 0)
    (transform := fun value => UInt64.ofNat (Nat.gcd value.toNat 42))
    (expected := LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected)
    (module_ := LeanExeGen.GeneratedR4337040846e16beb.«module»)
    (env := env) (initial := initial) (inputPtr := inputPtr) (input := input)
    (heapTop := heapTop) (allocs := allocs)
    (hInput := hArray) (hFitMemory := hOutputFitMemory) (hPages := hPages)
    (hMemory32 := rfl) (hHeapTop := hHeapTop) (hFreeList := hFreeList)
    (hAllocs := hAllocs)
  · intro value
    exact scalar_correct env initial value
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]
  · intro hSize
    simp [LeanExeGen.GeneratedR4337040846e16beb.FormalSpec.expected, hSize]

end LeanExeGen.GeneratedR4337040846e16beb.Behavior
