import Project.EulerGridStep.MixedState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Each exact mixed write consumes a reusable node or, on the sixth field, fresh memory. -/
theorem mixed_cell_fresh_call {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused heapTop allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index field : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hField : field < 6) (hi : 1 + 6 * index + 5 < output.size)
    (hState : MixedCellState initial heapTop roots output index cell field allocs releases frees)
    (hRoot : roots 6 = heapTop + 48)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size)
    (hFive : field = 5) :
    TerminatesWith env m 27 initial
      [.i64 ((Model.payload cell).getD field 0), .i64 (UInt64.ofNat field),
        .i64 (UInt64.ofNat index), .i64 (roots field), .i64 unused]
      (fun final values => values = [.i64 (roots (field + 1)), .i64 (roots (field + 1))] ∧
        MixedCellState final heapTop roots output index cell (field + 1) allocs releases frees ∧
        FieldResult (mixedChoice roots heapTop allocs output.size field) initial final
          (roots field) (cellPrefix output index cell field) (1 + 6 * index + field)
          ((Model.payload cell).getD field 0)) := by
  have hCurrent := hState.buffers.liveAt ⟨roots field, cellPrefix output index cell field⟩
    (cellLive_contains roots output index cell field field (by omega))
  have hLive : ∀ buffer ∈ cellLive roots output index cell field,
      ObjectsSeparate (roots (field + 1)) output.size buffer.root output.size := by
    apply cellLive_separate roots output index cell field (field + 1)
    intro k hk
    exact hSlots (field + 1) (by omega) k (by omega) (by omega)
  have hTarget : roots (field + 1) = heapTop + 48 := by simpa only [hFive] using hRoot
  have hEmpty : writerPool roots field = [] := by simp [writerPool, hFive]
  have hEmptyNext : writerPool roots (field + 1) = [] := by simp [writerPool, hFive]
  have hValid := fresh_valid_of_space initial heapTop (roots field) (allocs + UInt64.ofNat field)
    (cellPrefix output index cell field) (by simpa only [cellPrefix_size] using hState.space)
    hState.buffers.pages (by simpa [mixedHeap, hField] using hState.heap)
    (by simpa only [hEmpty, List.headD_nil] using hState.buffers.freeHead) hState.buffers.allocations
    (by simpa only [cellPrefix_size, hTarget] using
      hSlots (field + 1) (by omega) field (by omega) (by omega))
  have hCall := writeCellField_fresh_buffer_state layout env initial unused (roots field) heapTop
    (allocs + UInt64.ofNat field) releases frees (cellPrefix output index cell field)
    (cellLive roots output index cell field) index field ((Model.payload cell).getD field 0)
    hCurrent.2.2 (by rw [cellPrefix_size]; omega)
    (by simpa only [cellPrefix_size, hEmpty] using hState.buffers) hValid
    (by simpa only [cellPrefix_size, hTarget] using hLive)
  apply hCall.mono
  rintro final values ⟨hValues, hResult, hFinal, hHeap⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [hTarget] using hValues
  · simpa only [cellPrefix_size, cellLive, cellPrefix, hTarget, hEmptyNext,
      UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, UInt64.add_assoc] using hFinal
  · simpa [mixedHeap, cellPrefix_size, show ¬ field + 1 < 6 by omega] using hHeap
  · rw [hResult.pages]
    exact hState.space
  · simpa only [mixedChoice, ite_eq_right (by omega : ¬ field < 5), cellPrefix_size] using hResult

#print axioms mixed_cell_fresh_call
end Project.EulerGridStep.Execution
