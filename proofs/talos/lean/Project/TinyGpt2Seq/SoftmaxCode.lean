import Project.TinyGpt2Seq.Region
import Project.SequenceSoftmax.ComputeState

namespace Project.TinyGpt2Seq.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def softmaxEmpty : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 27 ++ FixedArrayAllocate.program 27 1 ++
  [.localGet 32, .localSet 23] ++ FixedArrayResult.lengthStoreProgram 23 0 ++
  [.localGet 23, .localSet 2, .localGet 2, .localSet 21, .localGet 2, .localSet 22]

def softmaxNonempty : Wasm.Program :=
  [
   .localGet 0,
   .localSet 3,
   .localGet 1,
   .localSet 4,
   .localGet 0,
   .localSet 5,
   .localGet 1,
   .localSet 6,
   .localGet 5,
   .localGet 6,
   .call 46,
   .localSet 7,
   .localGet 7,
   .localSet 8,
   .localGet 3,
   .localGet 4,
   .localGet 8,
   .call 44,
   .localSet 10,
   .localSet 9,
   .localGet 9,
   .localSet 11,
   .localGet 10,
   .localSet 12,
   .localGet 11,
   .localSet 13,
   .localGet 12,
   .localSet 14,
   .localGet 11,
   .localSet 15,
   .localGet 12,
   .localSet 16,
   .localGet 15,
   .localGet 16,
   .call 48,
   .localSet 17,
   .localGet 17,
   .localSet 18,
   .localGet 13,
   .localGet 14,
   .localGet 18,
   .call 47,
   .localSet 20,
   .localSet 19,
   .localGet 19,
   .localSet 21,
   .localGet 20,
   .localSet 22,
   .localGet 9,
   .constI64 0,
   .eqI64,
   .eqz,
   .iff 0 1 [.localGet 9, .localGet 21, .eqI64, .eqz] [.const 0] [] [.i32],
   .iff 0 0 [
    .localGet 9,
    .call 82
   ] []
  ]

theorem softmax_shape : func49 = func49.take 14 ++
    [.iff 0 0 softmaxEmpty softmaxNonempty, .localGet 21, .localGet 22] := rfl

def SoftmaxPost (heap : Heap) (initial : Store Unit) (input : Array UInt64)
    (remaining pageLimit : Nat) (final : Store Unit) (values : List Value) : Prop :=
  ∃ resultHeap result,
    values = [.i64 result.root, .i64 result.root] ∧ resultHeap.At final ∧
    resultHeap.OwnsWords final result (SequenceSoftmax.compute input) ∧
    heap.Frame initial resultHeap final ∧
    OutputBudget final resultHeap remaining pageLimit module

#print axioms softmax_shape
end Project.TinyGpt2Seq.Spec
