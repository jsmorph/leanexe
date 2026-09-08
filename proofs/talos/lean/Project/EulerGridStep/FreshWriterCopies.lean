import Project.EulerGridStep.FreshCellState
import Project.EulerGridStep.WriterSequence

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The first cell's six emitted writes allocate all six fresh slots and preserve the old grid. -/
theorem fresh_writer_copies_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (base : Nat) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hi : 1 + 6 * index + 5 < output.size)
    (hState : FreshCellState initial base output index cell 0 allocs releases frees)
    (observedRoot : UInt64) (observed : Array UInt64)
    (hObserved : UInt64Array.At initial observedRoot observed)
    (hSeparate : ∀ a ≤ 6, ObjectsSeparate (arenaRoot base output.size a) output.size observedRoot observed.size)
    (Q : Assertion Unit) (after : Wasm.Program)
    (hNext : ∀ final, FreshCellState final base output index cell 6 allocs releases frees →
      UInt64Array.At final observedRoot observed →
      wp m (writerAcceptedBody.drop 126 ++ after) Q final
        (writerStageFrame (arenaRoot base output.size) unused index cell 5) env) :
    wp m (writerAcceptedBody ++ after) Q initial
      (writerEntryFrame unused (arenaRoot base output.size 0) index cell) env := by
  apply writer_sequence_spec m env initial unused (arenaRoot base output.size) index cell
    (fun field current => FreshCellState current base output index cell field allocs releases frees ∧
      UInt64Array.At current observedRoot observed) ⟨hState, hObserved⟩
  · intro field hField current hCurrent
    apply (fresh_cell_field_call layout env current
      (writerCallUnused unused (arenaRoot base output.size) field) allocs releases frees
      base output index field cell hField hi hCurrent.1).mono
    rintro final values ⟨hValues, hFinal, hResult⟩
    refine ⟨hValues, hFinal, hResult.preserves_array observedRoot observed hCurrent.2 ?_⟩
    simpa only [FieldAllocation.root, cellPrefix_size, arena_root_eq_heap] using
      hSeparate (field + 1) (by omega)
  · intro final hFinal
    exact hNext final hFinal.1 hFinal.2

#print axioms fresh_writer_copies_spec
end Project.EulerGridStep.Execution
