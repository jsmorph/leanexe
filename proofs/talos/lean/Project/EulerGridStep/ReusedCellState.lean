import Project.EulerGridStep.ReusedState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

theorem reused_cell_field_call {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused heapTop allocs releases frees : UInt64)
    (roots : Nat → UInt64) (output : Array UInt64) (index field : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hField : field < 6) (hi : 1 + 6 * index + 5 < output.size)
    (hState : ReusedCellState initial heapTop roots output index cell field allocs releases frees)
    (hSlots : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) output.size (roots b) output.size) :
    TerminatesWith env m 27 initial
      [.i64 ((Model.payload cell).getD field 0), .i64 (UInt64.ofNat field),
        .i64 (UInt64.ofNat index), .i64 (roots field), .i64 unused]
      (fun final values => values = [.i64 (roots (field + 1)), .i64 (roots (field + 1))] ∧
        ReusedCellState final heapTop roots output index cell (field + 1) allocs releases frees ∧
        FieldResult (reusedChoice roots allocs output.size field) initial final
          (roots field) (cellPrefix output index cell field) (1 + 6 * index + field)
          ((Model.payload cell).getD field 0)) := by
  have hCurrent := hState.buffers.liveAt ⟨roots field, cellPrefix output index cell field⟩
    (cellLive_contains roots output index cell field field (by omega))
  have hLive : ∀ buffer ∈ cellLive roots output index cell field,
      ObjectsSeparate (roots (field + 1)) output.size buffer.root output.size := by
    apply cellLive_separate roots output index cell field (field + 1)
    intro k hk
    exact hSlots (field + 1) (by omega) k (by omega) (by omega)
  have hBuffers := hState.buffers
  rw [reusePool_head roots field hField] at hBuffers
  have hRest := reusePool_separate roots output.size (field + 1) (field + 1) (by omega) (by omega) hSlots
  have hSource := hSlots (field + 1) (by omega) field (by omega) (by omega)
  have hCall := writeCellField_buffer_state layout env initial unused (roots field) (roots (field + 1))
    (allocs + UInt64.ofNat field) releases frees (cellPrefix output index cell field)
    (cellLive roots output index cell field) (reusePool roots (field + 1)) index field
    ((Model.payload cell).getD field 0) hCurrent.2.2 (by rw [cellPrefix_size]; omega)
    (by simpa only [cellPrefix_size] using hBuffers)
    (by simpa only [cellPrefix_size] using hSource)
    (by simpa only [cellPrefix_size] using hLive)
    (by simpa only [cellPrefix_size] using hRest)
  apply hCall.mono
  rintro final values ⟨hValues, hResult, hFinal⟩
  have hHeap := (hResult.reused_buffers
    (by simpa only [cellPrefix_size] using hBuffers)
    (by simpa only [cellPrefix_size] using hLive)
    (by simpa only [cellPrefix_size] using hRest)).2
  refine ⟨hValues, ⟨?_, ?_⟩, ?_⟩
  · simpa only [cellPrefix_size, cellLive, cellPrefix, UInt64.ofNat_add,
      show UInt64.ofNat 1 = 1 from rfl, UInt64.add_assoc] using hFinal
  · rw [hHeap]
    exact hState.heap
  · simpa only [reusedChoice, cellPrefix_size] using hResult

#print axioms reused_cell_field_call
end Project.EulerGridStep.Execution
