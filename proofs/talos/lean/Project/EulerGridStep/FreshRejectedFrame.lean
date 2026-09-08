import Project.EulerGridStep.RejectedFrame
import Project.EulerGridStep.RejectedAllocationBump

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit.FixedArrayCopy

theorem rejected_fresh_allocated_frame (unused source heapTop : UInt64) (count index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) :
    RejectedTailFrame
      (rejectedFreshAllocFrame (rejectedReadyFrame unused source count index cell) heapTop (fieldRequest count))
      source (heapTop + 48) count := by
  constructor <;>
    simp [rejectedFreshAllocFrame, rejectedFreshBumpFrame, rejectedReadyFrame,
      rejectedCapacityFrame, rejectedPrefixFrame, writerEntryFrame, writerParameters, Locals.get]

def rejectedFreshReturnedFrame (unused source heapTop : UInt64) (count index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : Locals :=
  { counterFrame
      (rejectedFreshAllocFrame (rejectedReadyFrame unused source count index cell) heapTop (fieldRequest count))
      72 count (rejected_fresh_allocated_frame unused source heapTop count index cell).counter with
    values := [.i64 (heapTop + 48)] }

#print axioms rejected_fresh_allocated_frame
end Project.EulerGridStep.Execution
