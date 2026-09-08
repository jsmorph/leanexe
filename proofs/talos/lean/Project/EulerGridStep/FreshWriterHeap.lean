import Project.EulerGridStep.FreshWriterFramed

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The complete first writer retains the next heap address as well as the old grid. -/
theorem writeCell_fresh_accepted_heap {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused allocs releases frees : UInt64)
    (base : Nat) (output : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hAccepted : cell.status = 0) (hi : 1 + 6 * index + 5 < output.size)
    (hState : FreshCellState initial base output index cell 0 allocs releases frees)
    (observedRoot : UInt64) (observed : Array UInt64)
    (hObserved : UInt64Array.At initial observedRoot observed)
    (hSeparate : ∀ a ≤ 6, ObjectsSeparate (arenaRoot base output.size a) output.size observedRoot observed.size) :
    TerminatesWith env m 34 initial
      [.i64 cell.courant, .i64 cell.alpha, .i64 cell.pressure, .i64 cell.energy,
        .i64 cell.momentum, .i64 cell.density, .i64 cell.status, .i64 (UInt64.ofNat index),
        .i64 (arenaRoot base output.size 0), .i64 unused]
      (fun final values =>
        values = [.i64 (arenaRoot base output.size 6), .i64 (arenaRoot base output.size 6)] ∧
        BufferState final output.size
          [⟨arenaRoot base output.size 6, Model.putCell output index cell⟩,
            ⟨arenaRoot base output.size 0, output⟩]
          [arenaRoot base output.size 1, arenaRoot base output.size 2, arenaRoot base output.size 3,
            arenaRoot base output.size 4, arenaRoot base output.size 5]
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.globals.globals[0]? = some (.i64 (arenaHeap base output.size 7)) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final observedRoot observed) := by
  apply writeCell_fresh_framed layout env initial unused allocs releases frees base output index cell
    hAccepted hi hState (fun current => UInt64Array.At current observedRoot observed) hObserved
  · intro field hField current final hOld hResult
    apply hResult.preserves_array observedRoot observed hOld
    simpa only [FieldAllocation.root, cellPrefix_size, arena_root_eq_heap] using
      hSeparate (field + 1) (by omega)
  · intro count hLo hHi current final hOld hResult
    apply hResult.preserves_array observedRoot observed hOld
    simpa only [cellPrefix_size] using hSeparate count (by omega)

#print axioms writeCell_fresh_accepted_heap
end Project.EulerGridStep.Execution
