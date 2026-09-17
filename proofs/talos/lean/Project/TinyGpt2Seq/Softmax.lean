import Project.TinyGpt2Seq.SoftmaxNonempty
import Project.TinyGpt2Seq.SoftmaxEmpty

namespace Project.TinyGpt2Seq.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution Project.SequenceSoftmax.Spec

theorem softmax_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner : UInt64) (source : FreeNode) (input : Array UInt64) (remaining pageLimit : Nat)
    (hHeap : heap.At initial) (hInput : heap.OwnsWords initial source input)
    (hBudget : OutputBudget initial heap (computeBytes input.size+remaining) pageLimit module) :
    TerminatesWith env module 49 initial [.i64 source.root, .i64 owner]
      (SoftmaxPost heap initial input remaining pageLimit) := by
  by_cases hEmpty : input = #[]
  · subst input
    exact softmax_empty_exact env initial heap owner source remaining pageLimit hHeap hInput hBudget
  · exact softmax_nonempty_exact env initial heap owner source input remaining pageLimit hHeap hInput
      (by have := Array.size_eq_zero_iff.not.mpr hEmpty; omega) hBudget

#print axioms softmax_exact
end Project.TinyGpt2Seq.Spec
