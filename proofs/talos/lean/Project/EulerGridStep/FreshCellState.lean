import Project.EulerGridStep.FreshBufferState
import Project.EulerGridStep.ArenaAllocation
import Project.EulerGridStep.CellPrefixes

namespace Project.EulerGridStep.Execution
open Wasm

/-- The initialized output prefixes and next unused slot during the first cell's fresh writes. -/
structure FreshCellState (current : Store Unit) (base : Nat) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (field : Nat) (allocs releases frees : UInt64) : Prop where
  buffers : BufferState current output.size (cellLive (arenaRoot base output.size) output index cell field)
    [] (allocs + UInt64.ofNat field) releases frees
  heap : current.globals.globals[0]? = some (.i64 (arenaHeap base output.size (field + 1)))
  budget : base + 7 * arenaObjectSize output.size ≤ current.mem.pages * 65536

/-- One exact fresh field call initializes the next arena slot and advances the staged invariant. -/
theorem fresh_cell_field_call {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (base : Nat) (output : Array UInt64) (index field : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hField : field < 6) (hi : 1 + 6 * index + 5 < output.size)
    (hState : FreshCellState initial base output index cell field allocs releases frees) :
    TerminatesWith env m 27 initial
      [.i64 ((Model.payload cell).getD field 0), .i64 (UInt64.ofNat field),
        .i64 (UInt64.ofNat index), .i64 (arenaRoot base output.size field), .i64 unused]
      (fun final values =>
        values = [.i64 (arenaRoot base output.size (field + 1)), .i64 (arenaRoot base output.size (field + 1))] ∧
        FreshCellState final base output index cell (field + 1) allocs releases frees ∧
        FieldResult (.fresh (arenaHeap base output.size (field + 1)) (allocs + UInt64.ofNat field))
          initial final (arenaRoot base output.size field) (cellPrefix output index cell field)
          (1 + 6 * index + field) ((Model.payload cell).getD field 0)) := by
  have hCurrent := hState.buffers.liveAt
    ⟨arenaRoot base output.size field, cellPrefix output index cell field⟩
    (cellLive_contains (arenaRoot base output.size) output index cell field field (by omega))
  have hBudget := hState.budget
  have hPages := hState.buffers.pages
  have hBudget32 : base + 7 * arenaObjectSize output.size ≤ 4294967296 := by omega
  have hValid := arena_fresh_valid initial base output.size (field + 1) field
    (allocs + UInt64.ofNat field) (cellPrefix output index cell field) (cellPrefix_size _ _ _ _)
    (by omega) (by omega) (by omega) hBudget hPages hState.heap
    (by simpa using hState.buffers.freeHead) hState.buffers.allocations
  have hLive : ∀ buffer ∈ cellLive (arenaRoot base output.size) output index cell field,
      ObjectsSeparate (arenaRoot base output.size (field + 1)) output.size buffer.root output.size := by
    apply cellLive_separate (arenaRoot base output.size) output index cell field (field + 1)
    intro k hk
    exact arena_roots_separate base output.size (field + 1) k (by omega) (by omega) (by omega) hBudget32
  have hCall := writeCellField_fresh_buffer_state layout env initial unused (arenaRoot base output.size field)
    (arenaHeap base output.size (field + 1)) (allocs + UInt64.ofNat field) releases frees
    (cellPrefix output index cell field) (cellLive (arenaRoot base output.size) output index cell field)
    index field ((Model.payload cell).getD field 0) hCurrent.2.2 (by rw [cellPrefix_size]; omega)
    (by simpa only [cellPrefix_size] using hState.buffers) hValid
    (by simpa only [cellPrefix_size, arena_root_eq_heap] using hLive)
  apply hCall.mono
  rintro final values ⟨hValues, hResult, hBuffers, hHeap⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, hResult⟩
  · simpa only [arena_root_eq_heap] using hValues
  · simpa only [cellPrefix_size, cellLive, cellPrefix, arena_root_eq_heap,
      UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl, UInt64.add_assoc] using hBuffers
  · simpa only [cellPrefix_size, arena_heap_succ] using hHeap
  · rw [hResult.pages]
    exact hState.budget

#print axioms fresh_cell_field_call
end Project.EulerGridStep.Execution
