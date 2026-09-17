import Project.SequenceSoftmax.ComputeNonempty
import Project.SequenceSoftmax.ComputeEmpty

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem compute_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (input : Array UInt64) (remaining pageLimit : Nat)
    (hHeap : heap.At initial) (hInput : heap.OwnsWords initial source input)
    (hBudget : OutputBudget initial heap (computeBytes input.size+remaining) pageLimit module) :
    TerminatesWith env module 11 initial [.i64 source.root]
      (ComputePost heap initial input remaining pageLimit) := by
  by_cases hEmpty : input = #[]
  · subst input
    exact compute_empty_exact env initial heap source remaining pageLimit hHeap hInput hBudget
  · exact compute_nonempty_exact env initial heap source input remaining pageLimit hHeap hInput
      (by have := Array.size_eq_zero_iff.not.mpr hEmpty; omega) hBudget

#print axioms compute_exact
end Project.SequenceSoftmax.Spec
