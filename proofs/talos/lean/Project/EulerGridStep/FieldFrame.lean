import Project.EulerGridStep.AllocationChoice
import Project.EulerGridStep.FieldPrefix
import Project.EulerGridStep.FieldCapacity
import Project.EulerGridStep.FieldTail

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Live frame at the start of allocation, after the accepted bounds branch. -/
def fieldReadyFrame (unused source : UInt64) (count index field : Nat) (value : UInt64) : Locals :=
  fieldCapacityFrame { fieldPrefixFrame unused source count index field value with values := [] }
    (UInt64.ofNat count)

structure FieldTailFrame (frame : Locals) (source target : UInt64)
    (count index : Nat) (value : UInt64) : Prop where
  params : frame.params.length = 5
  locals : frame.locals.length = 20
  values : frame.values = []
  sourceGet : frame.get 10 = some (.i64 source)
  targetGet : frame.get 14 = some (.i64 target)
  indexGet : frame.get 11 = some (.i64 (UInt64.ofNat index))
  lengthGet : frame.get 12 = some (.i64 (UInt64.ofNat count))
  countGet : frame.get 13 = some (.i64 (UInt64.ofNat count))
  valueGet : frame.get 16 = some (.i64 value)

theorem field_ready_shape (unused source : UInt64) (count index field : Nat) (value : UInt64)
    (hFit : 8 * (count + 1) ≤ 4294967296) :
    (fieldReadyFrame unused source count index field value).params.length = 5 ∧
    (fieldReadyFrame unused source count index field value).locals.length = 20 ∧
    (fieldReadyFrame unused source count index field value).values = [] ∧
    (fieldReadyFrame unused source count index field value).locals[14]? = some (.i64 (fieldRequest count)) := by
  simp [fieldReadyFrame, fieldCapacityFrame, fieldPrefixFrame, fieldParameters,
    scalar_capacity_word count hFit, fieldRequest]

theorem field_allocated_frame (choice : FieldAllocation) (unused source : UInt64)
    (count index field : Nat) (value : UInt64) :
    FieldTailFrame (choice.frame (fieldReadyFrame unused source count index field value) count)
      source choice.root count (1 + 6 * index + field) value := by
  cases choice <;> constructor <;>
    simp [FieldAllocation.frame, FieldAllocation.root, fieldReadyFrame, fieldCapacityFrame,
      fieldPrefixFrame, fieldParameters, fieldAllocFrame, fieldBumpFrame,
      reuseAllocFrame, reuseFoundFrame, reuseChosenFrame, reuseLoadedFrame, reuseSearchFrame]

theorem FieldTailFrame.counter {frame : Locals} {source target : UInt64}
    {count index : Nat} {value : UInt64} (h : FieldTailFrame frame source target count index value) :
    frame.validIndex 15 := by
  change 15 < frame.params.length + frame.locals.length
  rw [h.params, h.locals]
  decide

#print axioms field_ready_shape
#print axioms field_allocated_frame
#print axioms FieldTailFrame.counter
end Project.EulerGridStep.Execution
