import Project.EulerGridStep.BufferState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A reused clone advances the buffer state and preserves the next fresh heap address. -/
theorem FieldResult.reused_buffers {initial final : Store Unit}
    {source root allocs releases frees : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    {live : List LiveBuffer} {rest : List UInt64}
    (hResult : FieldResult (.reuse root (fieldRequest input.size) (rest.headD 0) allocs)
      initial final source input index value)
    (hState : BufferState initial input.size live (root :: rest) allocs releases frees)
    (hLive : ∀ buffer ∈ live, ObjectsSeparate root input.size buffer.root input.size)
    (hFree : ∀ other ∈ rest, ObjectsSeparate root input.size other input.size) :
    BufferState final input.size (⟨root, input.set! index value⟩ :: live) rest
      (allocs + 1) releases frees ∧
      final.globals.globals[0]? = initial.globals.globals[0]? := by
  have hGlobals : final.globals.globals =
      (initial.globals.globals.set 1 (.i64 (rest.headD 0))).set 2 (.i64 (allocs + 1)) := by
    simpa only [FieldAllocation.store, reuseAllocatedStore, reuseStore, writeAllocationHeader,
      writeHeaderWord, reuseUnlinkedStore] using hResult.globals
  have hGlobalLength := (List.getElem?_eq_some_iff.mp hState.frees).choose
  refine ⟨⟨hResult.add_live_buffer rfl live hState.liveAt hLive,
    hResult.preserves_free_chain input.size rest hState.chain.2.2.2 hFree, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hGlobals]
    simpa [List.getElem?_set] using hState.releases
  · rw [hGlobals]
    simpa [List.getElem?_set] using hState.frees
  · rw [hResult.pages]
    exact hState.pages
  · rw [hGlobals]
    simp

/-- A fresh clone advances the same buffer state and records the exact new heap address. -/
theorem FieldResult.fresh_buffers {initial final : Store Unit}
    {source heapTop allocs releases frees : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    {live : List LiveBuffer}
    (hResult : FieldResult (.fresh heapTop allocs) initial final source input index value)
    (hState : BufferState initial input.size live [] allocs releases frees)
    (hLive : ∀ buffer ∈ live, ObjectsSeparate (heapTop + 48) input.size buffer.root input.size) :
    BufferState final input.size (⟨heapTop + 48, input.set! index value⟩ :: live) []
      (allocs + 1) releases frees ∧
      final.globals.globals[0]? = some (.i64 (heapTop + 48 + fieldRequest input.size)) := by
  have hGlobals : final.globals.globals =
      (initial.globals.globals.set 0 (.i64 (heapTop + 48 + fieldRequest input.size))).set 2 (.i64 (allocs + 1)) := by
    simpa only [FieldAllocation.store, FixedArrayAllocator.allocStore] using hResult.globals
  have hGlobalLength := (List.getElem?_eq_some_iff.mp hState.frees).choose
  refine ⟨⟨hResult.add_live_buffer rfl live hState.liveAt hLive, trivial, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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

#print axioms FieldResult.reused_buffers
#print axioms FieldResult.fresh_buffers
end Project.EulerGridStep.Execution
