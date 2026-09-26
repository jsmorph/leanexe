import Project.Drone.ExecutionPushBudget
import Project.Drone.ExecutionPreserveWords

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.EulerRiemann.Execution

/-- A newly allocated result with the caller's live arrays and unused budget preserved. -/
def FreshArrayResult (initialHeap : Heap) (initial : Store Unit) (output : Array UInt64)
    (remaining pageLimit : Nat) (final : Store Unit) (values : List Value) : Prop :=
  ∃ (heap : Heap) (node : FreeNode), heap.At final ∧ Budget final heap remaining pageLimit ∧
    heap.OwnsWords final node output ∧ PreservesWords initialHeap initial heap final ∧
    SeparateWords initialHeap initial node ∧ values = [.i64 node.root, .i64 node.root]

end Project.Drone.Execution
