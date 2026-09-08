import Project.EulerGridStep.WriterPool
import Project.EulerGridStep.BufferResults
import Project.EulerGridStep.FreshBufferState
import Project.EulerGridStep.FreshSpace

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

def mixedHeap (heapTop : UInt64) (count field : Nat) : UInt64 :=
  if field < 6 then heapTop else heapTop + 48 + fieldRequest count

def mixedChoice (roots : Nat → UInt64) (heapTop allocs : UInt64) (count field : Nat) : FieldAllocation :=
  if field < 5 then .reuse (roots (field + 1)) (fieldRequest count)
    ((writerPool roots (field + 1)).headD 0) (allocs + UInt64.ofNat field)
  else .fresh heapTop (allocs + UInt64.ofNat field)

structure MixedCellState (current : Store Unit) (heapTop : UInt64) (roots : Nat → UInt64)
    (output : Array UInt64) (index : Nat) (cell : Project.EulerCellStep.Model.CheckedCell)
    (field : Nat) (allocs releases frees : UInt64) : Prop where
  buffers : BufferState current output.size (cellLive roots output index cell field)
    (writerPool roots field) (allocs + UInt64.ofNat field) releases frees
  heap : current.globals.globals[0]? = some (.i64 (mixedHeap heapTop output.size field))
  space : heapTop.toNat + 48 + 8 * (output.size + 1) ≤ current.mem.pages * 65536

end Project.EulerGridStep.Execution
