import Project.EulerGridStep.RejectedPrefix
import Project.EulerGridStep.RejectedCapacity
import Project.EulerGridStep.RejectedAllocationReuse

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

def rejectedReadyFrame (unused source : UInt64) (count index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : Locals :=
  rejectedCapacityFrame
    { rejectedPrefixFrame (writerEntryFrame unused source index cell) source count with values := [] }
    (UInt64.ofNat count)

structure RejectedTailFrame (frame : Locals) (source target : UInt64) (count : Nat) : Prop where
  params : frame.params.length = 10
  locals : frame.locals.length = 72
  values : frame.values = []
  sourceGet : frame.get 67 = some (.i64 source)
  targetGet : frame.get 71 = some (.i64 target)
  indexGet : frame.get 68 = some (.i64 0)
  lengthGet : frame.get 69 = some (.i64 (UInt64.ofNat count))
  countGet : frame.get 70 = some (.i64 (UInt64.ofNat count))
  valueGet : frame.get 73 = some (.i64 1)

theorem rejected_ready_shape (unused source : UInt64) (count index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (hFit : 8 * (count + 1) ≤ 4294967296) :
    (rejectedReadyFrame unused source count index cell).params.length = 10 ∧
    (rejectedReadyFrame unused source count index cell).locals.length = 72 ∧
    (rejectedReadyFrame unused source count index cell).values = [] ∧
    (rejectedReadyFrame unused source count index cell).locals[66]? = some (.i64 (fieldRequest count)) := by
  simp [rejectedReadyFrame, rejectedCapacityFrame, rejectedPrefixFrame, writerEntryFrame,
    writerParameters, scalar_capacity_word count hFit, fieldRequest]

theorem rejected_allocated_frame (unused source root capacity next : UInt64) (count index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) :
    RejectedTailFrame
      (rejectedReuseAllocFrame (rejectedReadyFrame unused source count index cell) root capacity next)
      source root count := by
  constructor <;>
    simp [rejectedReuseAllocFrame, rejectedReuseFoundFrame, rejectedReuseChosenFrame,
      rejectedReuseLoadedFrame, rejectedReuseSearchFrame, rejectedReadyFrame,
      rejectedCapacityFrame, rejectedPrefixFrame, writerEntryFrame, writerParameters, Locals.get]

theorem RejectedTailFrame.counter {frame : Locals} {source target : UInt64}
    {count : Nat} (h : RejectedTailFrame frame source target count) : frame.validIndex 72 := by
  change 72 < frame.params.length + frame.locals.length
  rw [h.params, h.locals]
  decide

#print axioms rejected_ready_shape
#print axioms rejected_allocated_frame
#print axioms RejectedTailFrame.counter
end Project.EulerGridStep.Execution
