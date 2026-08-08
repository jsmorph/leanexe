import Project.ProofKit.FixedArrayLengthDispatch
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.FixedArraySingleton
import Project.ProofKit.FixedArrayTraversalInput

namespace Project.ProofKit.FixedArraySingletonWrapper

open Wasm

def entryFrame (inputPtr : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := List.replicate 14 (.i64 0)
    values := [] }

def invalidProgram : Wasm.Program :=
  [.localGet 0, .localSet 4]

def scalarPrefix (callee : Nat) : Wasm.Program :=
  [
  .localSet 1,
  .localGet 1,
  .call callee,
  .localSet 2,
  .constI64 8,
  .constI64 1,
  .constI64 1,
  .mulI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .constI64 7,
  .addI64,
  .constI64 8,
  .divUI64,
  .constI64 8,
  .mulI64,
  .localSet 9,
  .localGet 9,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 9
  ] []
  ]

def validProgram (callee : Nat) : Wasm.Program :=
  FixedArrayTraversalInput.program 0 0 ++ scalarPrefix callee ++
    FixedArrayAllocator.region 1 ++ FixedArraySingleton.resultSuffix

def wrapperProgram (callee : Nat) : Wasm.Program :=
  FixedArrayLengthDispatch.eqProgram 5 1 invalidProgram
    (validProgram callee) ++ [.localGet 4]

def allocatorEntryFrame (inputPtr inputValue result : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := [
      .i64 inputValue, .i64 result, .i64 0, .i64 0, .i64 inputPtr,
      .i64 0, .i64 0, .i64 0, .i64 16, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0]
    values := [] }

def loadedFrame (inputPtr inputValue : UInt64) : Locals :=
  { params := [.i64 inputPtr]
    locals := [
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 inputPtr, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
    values := [.i64 inputValue] }

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1048576 in
set_option Elab.async false in
theorem wrapperProgram_spec
    (callee : Nat) (transform : UInt64 → UInt64)
    (expected : Array UInt64 → Array UInt64)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (inputPtr : UInt64) (input : Array UInt64) (heapTop allocs : UInt64)
    (hInput : UInt64Array.At initial inputPtr input)
    (hFitMemory : heapTop.toNat + 48 + 8 * ((expected input).size + 1) ≤
      initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (hCallee : ∀ value,
      TerminatesWith env module_ callee initial [.i64 value]
        (fun final results =>
          final = initial ∧ results = [.i64 (transform value)]))
    (hInvalid : input.size ≠ 1 → expected input = input)
    (hValid : ∀ hSize : input.size = 1,
      expected input = #[transform input[0]]) :
    wp module_ (wrapperProgram callee)
      (FixedArrayPairResult.publicPost (expected input))
      initial (entryFrame inputPtr) env := by
  unfold wrapperProgram
  apply FixedArrayLengthDispatch.eqProgram_spec 5 1 _ _ _
    module_ env initial (entryFrame inputPtr) inputPtr input
  · rfl
  · rfl
  · decide
  · simp [entryFrame]
  · decide
  · exact hInput
  · intro hSize
    have hExpected := hInvalid hSize
    unfold invalidProgram
    wp_run
    simp [FixedArrayLengthDispatch.branchFrame, entryFrame]
    rw [hExpected]
    simp only [FixedArrayEqNode.branchPost]
    wp_run
    exact ⟨inputPtr, rfl, hInput⟩
  · intro hSize
    have hIndex : 0 < input.size := by omega
    have hExpected := hValid hSize
    have hFitResult : heapTop.toNat + 48 + 16 ≤
        initial.mem.pages * 65536 := by
      rw [hExpected] at hFitMemory
      simpa using hFitMemory
    change wp module_ (validProgram callee) _ initial
      (FixedArrayLengthDispatch.branchFrame 5 (entryFrame inputPtr) inputPtr) env
    unfold validProgram
    rw [List.append_assoc]
    refine FixedArrayTraversalInput.program_spec
      (offset := 0) (module_ := module_) (env := env) (st := initial)
      (frame := FixedArrayLengthDispatch.branchFrame 5
        (entryFrame inputPtr) inputPtr)
      (inputPtr := inputPtr) (input := input) (index := 0)
      (hInput := hInput) (hIndex := hIndex)
      (Q := FixedArrayEqNode.branchPost module_ env [.localGet 4]
        (FixedArrayPairResult.publicPost (expected input)))
      (rest := scalarPrefix callee ++ FixedArrayAllocator.region 1 ++
        FixedArraySingleton.resultSuffix) ?_ ?_ ?_ ?_
    · simp [FixedArrayLengthDispatch.branchFrame, entryFrame]
    · simp [FixedArrayLengthDispatch.branchFrame, entryFrame]
    · rfl
    · unfold scalarPrefix
      change wp module_ _ _ initial (loadedFrame inputPtr input[0]) env
      unfold loadedFrame
      simp only [List.cons_append, List.nil_append]
      wp_run
      apply Wasm.wp_call_tw (hCallee input[0])
      rintro st values hResult
      rcases hResult with ⟨hStore, hValues⟩
      subst st
      subst values
      wp_run
      simp
      refine Wasm.wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      rw [wp_nil]
      change wp module_
        (FixedArrayAllocator.region 1 ++ FixedArraySingleton.resultSuffix)
        _ initial (allocatorEntryFrame inputPtr input[0] (transform input[0])) env
      apply FixedArraySingleton.region_result_spec module_ env initial
        (allocatorEntryFrame inputPtr input[0] (transform input[0]))
        heapTop allocs (transform input[0])
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact hFitResult
      · exact hPages
      · exact hMemory32
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs
      · intro hResult
        simp [allocatorEntryFrame, FixedArraySingleton.resultFrame,
          FixedArrayAllocator.allocFrame]
        rw [hExpected]
        simp only [FixedArrayEqNode.branchPost]
        wp_run
        exact ⟨heapTop + 48, rfl, hResult⟩

end Project.ProofKit.FixedArraySingletonWrapper
