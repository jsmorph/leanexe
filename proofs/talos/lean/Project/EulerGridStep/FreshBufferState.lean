import Project.EulerGridStep.BufferState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A fresh clone preserves the live list, keeps the free list empty, and advances the heap. -/
theorem writeCellField_fresh_buffer_state {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (unused source heapTop allocs releases frees : UInt64)
    (input : Array UInt64) (live : List LiveBuffer) (index field : Nat) (value : UInt64)
    (hInput : UInt64Array.At initial source input) (hi : 1 + 6 * index + field < input.size)
    (hState : BufferState initial input.size live [] allocs releases frees)
    (hValid : (FieldAllocation.fresh heapTop allocs).Valid initial source input)
    (hLive : ∀ buffer ∈ live, ObjectsSeparate (heapTop + 48) input.size buffer.root input.size) :
    TerminatesWith env m 27 initial
      [.i64 value, .i64 (UInt64.ofNat field), .i64 (UInt64.ofNat index), .i64 source, .i64 unused]
      (fun final values => values = [.i64 (heapTop + 48), .i64 (heapTop + 48)] ∧
        FieldResult (.fresh heapTop allocs) initial final source input (1 + 6 * index + field) value ∧
        BufferState final input.size
          (⟨heapTop + 48, input.set! (1 + 6 * index + field) value⟩ :: live) []
          (allocs + 1) releases frees ∧
        final.globals.globals[0]? = some (.i64 (heapTop + 48 + fieldRequest input.size))) := by
  apply (writeCellField_exact_in_module layout (.fresh heapTop allocs) env initial unused source
    input index field value hInput hi hValid hState.pages).mono
  rintro final values ⟨hValues, hResult⟩
  have hGlobals : final.globals.globals =
      (initial.globals.globals.set 0 (.i64 (heapTop + 48 + fieldRequest input.size))).set 2 (.i64 (allocs + 1)) := by
    simpa only [FieldAllocation.store, FixedArrayAllocator.allocStore] using hResult.globals
  have hGlobalLength := (List.getElem?_eq_some_iff.mp hState.frees).choose
  refine ⟨hValues, hResult, ?_, ?_⟩
  · refine ⟨hResult.add_live_buffer rfl live hState.liveAt hLive, trivial, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hGlobals]
      simpa [List.getElem?_set] using hState.freeHead
    · rw [hGlobals]
      simp (discharger := omega) [List.getElem?_set] <;> omega
    · rw [hGlobals]
      simpa [List.getElem?_set] using hState.releases
    · rw [hGlobals]
      simpa [List.getElem?_set] using hState.frees
    · rw [hResult.pages]
      exact hState.pages
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega

#print axioms writeCellField_fresh_buffer_state
end Project.EulerGridStep.Execution
