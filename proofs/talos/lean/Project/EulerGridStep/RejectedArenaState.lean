import Project.EulerGridStep.LaterArenaState

namespace Project.EulerGridStep.Execution
open Wasm

def rejectedHeapSlot (index : Nat) : Nat := if index = 0 then 2 else index + 6

def rejectedPool (base count index : Nat) : List UInt64 :=
  if index = 0 then [] else writerPool (arenaRoot base count) 1

/-- Rejection always returns slot one; its remaining pool and heap depend on the first-cell case. -/
structure RejectedArenaState (current : Store Unit) (base cells index : Nat) (output : Array UInt64)
    (allocs releases frees : UInt64) : Prop where
  buffers : BufferState current output.size [⟨arenaRoot base output.size 1, output⟩]
    (rejectedPool base output.size index) allocs releases frees
  heap : current.globals.globals[0]? = some (.i64 (arenaHeap base output.size (rejectedHeapSlot index)))
  budget : base + (cells + 6) * arenaObjectSize output.size ≤ current.mem.pages * 65536
  status : output[0]! = 1

theorem advanceAt_rejected_status (ratio : UInt64) (input output : Array UInt64) (index : Nat)
    (hRejected : (Model.cellAt ratio input index).status ≠ 0) (hNonempty : 0 < output.size) :
    (Model.advanceAt ratio input output index)[0]! = 1 := by
  simpa [Model.advanceAt, hRejected] using Array.getElem!_set!_self output 0 1 hNonempty

#print axioms advanceAt_rejected_status
end Project.EulerGridStep.Execution
