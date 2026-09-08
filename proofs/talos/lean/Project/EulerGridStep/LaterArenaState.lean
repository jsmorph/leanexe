import Project.EulerGridStep.LaterArena
import Project.EulerGridStep.MixedState
import Project.EulerGridStep.GridSizes

namespace Project.EulerGridStep.Execution
open Wasm

/-- State after a positive number of accepted cells; earlier final objects remain allocated. -/
structure LaterArenaState (current : Store Unit) (base cells completed : Nat) (output : Array UInt64)
    (allocs releases frees : UInt64) : Prop where
  buffers : BufferState current output.size [⟨arenaRoot base output.size (completed + 5), output⟩]
    (writerPool (arenaRoot base output.size) 0) allocs releases frees
  heap : current.globals.globals[0]? = some (.i64 (arenaHeap base output.size (completed + 6)))
  budget : base + (cells + 6) * arenaObjectSize output.size ≤ current.mem.pages * 65536

/-- Available space is needed only when the grid loop has another cell to process. -/
theorem LaterArenaState.mixed {current : Store Unit} {base cells completed : Nat} {output : Array UInt64}
    {allocs releases frees : UInt64} (hState : LaterArenaState current base cells completed output allocs releases frees)
    (cell : Project.EulerCellStep.Model.CheckedCell) (hLoop : completed < cells) :
    MixedCellState current (arenaHeap base output.size (completed + 6)) (laterRoots base output.size completed)
      output completed cell 0 allocs releases frees := by
  refine ⟨?_, ?_, later_fresh_space current base output.size cells completed hLoop hState.buffers.pages hState.budget⟩
  · simpa only [cellLive, later_root_zero, later_pool, show UInt64.ofNat 0 = 0 from rfl,
      UInt64.add_zero] using hState.buffers
  · simpa [mixedHeap] using hState.heap

#print axioms LaterArenaState.mixed
end Project.EulerGridStep.Execution
