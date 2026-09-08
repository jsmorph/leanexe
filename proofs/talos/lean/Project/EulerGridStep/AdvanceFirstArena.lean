import Project.EulerGridStep.AdvanceExecution
import Project.EulerGridStep.FreshWriterHeap
import Project.EulerGridStep.LaterArenaState

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The first accepted advance establishes the arena invariant used by every later cell. -/
theorem advanceAt_first_arena {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < input.size / 3)
    (hAccepted : (Model.cellAt ratio input 0).status = 0)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hBuffers : BufferState initial output.size [⟨arenaRoot base output.size 0, output⟩]
      [] allocs releases frees)
    (hHeap : initial.globals.globals[0]? = some (.i64 (arenaHeap base output.size 1)))
    (hBudget : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ initial.mem.pages * 65536)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 0, .i64 (arenaRoot base output.size 0), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values => values = [.i64 (arenaRoot base output.size 6), .i64 (arenaRoot base output.size 6)] ∧
        LaterArenaState final base (input.size / 3) 1 (Model.advanceAt ratio input output 0)
          (allocs + 6) (releases + 5) (frees + 5) ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input) := by
  have hReady : FreshCellState initial base output 0 (Model.cellAt ratio input 0) 0 allocs releases frees := by
    refine ⟨?_, hHeap, ?_⟩
    · simpa only [cellLive, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] using hBuffers
    · have hMul := Nat.mul_le_mul_right (arenaObjectSize output.size)
        (by omega : 7 ≤ input.size / 3 + 6)
      omega
  apply advanceAt_with_writer layout env initial ratio inputUnused pointer unused
    (arenaRoot base output.size 0) (arenaRoot base output.size 6) input 0 hInput hPositive
  have hWriter := writeCell_fresh_accepted_heap layout env initial unused allocs releases frees base
    output 0 (Model.cellAt ratio input 0) hAccepted (by omega) hReady pointer input hInput
    (fun a ha => hSeparate a (by omega))
  have hRun := hWriter.mono (fun final values hPost => by
    rcases hPost with ⟨hValues, hFinalBuffers, hFinalHeap, hPages, hInputFinal⟩
    have hKeep := hFinalBuffers.restrict_live
      [⟨arenaRoot base output.size 6, Model.putCell output 0 (Model.cellAt ratio input 0)⟩]
      (by intro buffer hb; obtain rfl := List.mem_singleton.mp hb; exact List.mem_cons_self)
    show values = [.i64 (arenaRoot base output.size 6), .i64 (arenaRoot base output.size 6)] ∧
      LaterArenaState final base (input.size / 3) 1 (Model.putCell output 0 (Model.cellAt ratio input 0))
        (allocs + 6) (releases + 5) (frees + 5) ∧
      final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input
    refine ⟨hValues, ⟨?_, ?_, ?_⟩, hPages, hInputFinal⟩
    · simpa only [putCell_size, writerPool, List.drop_zero] using hKeep
    · simpa only [putCell_size] using hFinalHeap
    · simpa only [putCell_size, hPages] using hBudget)
  simpa [advanceCellResult, Model.advanceAt, hAccepted] using hRun

#print axioms advanceAt_first_arena
end Project.EulerGridStep.Execution
