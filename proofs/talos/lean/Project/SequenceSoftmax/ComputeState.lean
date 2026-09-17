import Project.SequenceSoftmax.MapCalls

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def computeBytes (size : Nat) : Nat := 2*(48+8*(size+1))

def ComputePost (heap : Heap) (initial : Store Unit) (input : Array UInt64)
    (remaining pageLimit : Nat) (final : Store Unit) (values : List Value) : Prop :=
  ∃ resultHeap result,
    values = [.i64 result.root] ∧ resultHeap.At final ∧
    resultHeap.OwnsWords final result (compute input) ∧
    heap.Frame initial resultHeap final ∧
    OutputBudget final resultHeap remaining pageLimit module

end Project.SequenceSoftmax.Spec
