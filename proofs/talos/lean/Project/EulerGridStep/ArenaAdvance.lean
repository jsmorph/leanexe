import Project.EulerGridStep.AdvanceFirstArena
import Project.EulerGridStep.AdvanceArena
import Project.EulerGridStep.AdvanceFirstRejected
import Project.EulerGridStep.AdvanceLaterRejected

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

def arenaAdvanceRoot (base count index : Nat) (status : UInt64) : UInt64 :=
  if status = 0 then arenaRoot base count (index + 6) else arenaRoot base count 1

/-- Both exact storage outcomes of one cell call, with allocation and release counters. -/
def ArenaAdvanceState (current : Store Unit) (base cells index : Nat) (output : Array UInt64)
    (status allocs releases frees : UInt64) : Prop :=
  if status = 0 then LaterArenaState current base cells (index + 1) output
    (allocs + 6) (releases + 5) (frees + 5)
  else RejectedArenaState current base cells index output (allocs + 1) releases frees

/-- Complete first-cell control covers both numerical outcomes from initialized output storage. -/
theorem advanceAt_first_outcome {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hBuffers : BufferState initial output.size [⟨arenaRoot base output.size 0, output⟩]
      [] allocs releases frees)
    (hHeap : initial.globals.globals[0]? = some (.i64 (arenaHeap base output.size 1)))
    (hBudget : base + (input.size / 3 + 6) * arenaObjectSize output.size ≤ initial.mem.pages * 65536)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat 0), .i64 (arenaRoot base output.size 0), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values =>
        values = [.i64 (arenaAdvanceRoot base output.size 0 (Model.cellAt ratio input 0).status),
          .i64 (arenaAdvanceRoot base output.size 0 (Model.cellAt ratio input 0).status)] ∧
        ArenaAdvanceState final base (input.size / 3) 0 (Model.advanceAt ratio input output 0)
          (Model.cellAt ratio input 0).status allocs releases frees ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input) := by
  by_cases hAccepted : (Model.cellAt ratio input 0).status = 0
  · simpa only [arenaAdvanceRoot, ArenaAdvanceState, hAccepted, ite_true, Nat.zero_add,
      show UInt64.ofNat 0 = 0 from rfl] using
      advanceAt_first_arena layout env initial ratio inputUnused pointer unused allocs releases frees base input output
        hInput hPositive hAccepted hSize hBuffers hHeap hBudget hSeparate
  · simpa only [arenaAdvanceRoot, ArenaAdvanceState, hAccepted, ite_false, Nat.zero_add,
      show UInt64.ofNat 0 = 0 from rfl] using
      advanceAt_first_rejected_arena layout env initial ratio inputUnused pointer unused allocs releases frees base input output
        hInput hPositive hAccepted hSize hBuffers hHeap hBudget hSeparate

/-- Complete later-cell control covers either outcome while retaining the bounded arena. -/
theorem advanceAt_later_outcome {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit)
    (ratio inputUnused pointer unused allocs releases frees : UInt64)
    (base : Nat) (input output : Array UInt64) (index : Nat)
    (hInput : UInt64Array.At initial pointer input) (hPositive : 0 < index) (hi : index < input.size / 3)
    (hSize : output.size = 1 + 6 * (input.size / 3))
    (hState : LaterArenaState initial base (input.size / 3) index output allocs releases frees)
    (hSeparate : ∀ slot < input.size / 3 + 6,
      ObjectsSeparate (arenaRoot base output.size slot) output.size pointer input.size) :
    TerminatesWith env m 35 initial
      [.i64 (UInt64.ofNat index), .i64 (arenaRoot base output.size (index + 5)), .i64 unused,
        .i64 pointer, .i64 inputUnused, .i64 ratio]
      (fun final values =>
        values = [.i64 (arenaAdvanceRoot base output.size index (Model.cellAt ratio input index).status),
          .i64 (arenaAdvanceRoot base output.size index (Model.cellAt ratio input index).status)] ∧
        ArenaAdvanceState final base (input.size / 3) index (Model.advanceAt ratio input output index)
          (Model.cellAt ratio input index).status allocs releases frees ∧
        final.mem.pages = initial.mem.pages ∧ UInt64Array.At final pointer input) := by
  by_cases hAccepted : (Model.cellAt ratio input index).status = 0
  · simpa only [arenaAdvanceRoot, ArenaAdvanceState, hAccepted, ite_true, Nat.zero_add,
      show UInt64.ofNat 0 = 0 from rfl] using
      advanceAt_later_arena layout env initial ratio inputUnused pointer unused allocs releases frees base input output
        index hInput hPositive hi hAccepted hSize hState hSeparate
  · simpa only [arenaAdvanceRoot, ArenaAdvanceState, hAccepted, ite_false, Nat.zero_add,
      show UInt64.ofNat 0 = 0 from rfl] using
      advanceAt_later_rejected_arena layout env initial ratio inputUnused pointer unused allocs releases frees base input output
        index hInput hPositive hi hAccepted hSize hState hSeparate

#print axioms advanceAt_first_outcome
#print axioms advanceAt_later_outcome
end Project.EulerGridStep.Execution
