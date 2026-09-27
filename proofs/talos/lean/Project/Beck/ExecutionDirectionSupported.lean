import Project.Beck.ExecutionDirection
import Project.Beck.State

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem direction_matrix_bounds (input : Input) (point : Point) (supported : Project.Beck.State.Supported input)
    (nonempty : (Project.Beck.Counting.live input point).Nonempty) :
    (protectedMatrix input point).size ≤ 56 ∧ (protectedMatrix input point).size / input.jobs < 6 := by
  have short := Project.Beck.ProtectedMatrix.protectedMatrix_short input point supported.overlap nonempty
  have positive : 0 < input.jobs := by
    obtain ⟨job, _⟩ := nonempty
    exact (Nat.zero_le job.val).trans_lt job.isLt
  have rows : (protectedMatrix input point).size / input.jobs < 6 := short.trans_le supported.capacity
  have small : (protectedMatrix input point).size < 6 * input.jobs := (Nat.div_lt_iff_lt_mul positive).mp rows
  exact ⟨by nlinarith [supported.capacity], rows⟩

theorem direction_supported_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (nonempty : (Project.Beck.Counting.live input point).Nonempty)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (directionBytes input point + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 30 initial
      (matrixParams input point inputOwner inputPointer pointOwner pointPointer).reverse
      (fun final values => ∃ finalHeap node, finalHeap.At final ∧ finalHeap.OwnsWords final node (direction input point) ∧
        heap.Frame initial finalHeap final ∧ FreshFor heap node ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» ∧ values = [.i64 node.root, .i64 node.root]) := by
  have bounds := direction_matrix_bounds input point supported nonempty
  have basis := Project.Beck.ProtectedMatrix.source_basis_complete input point supported.overlap nonempty
  exact direction_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer remaining pageLimit
    valid pointArray pointProtected inputArray inputProtected pointSize inputSize supported.capacity categories overlap
    bounds.1 bounds.2 basis.1 ((Nat.le_of_lt basis.2.2).trans supported.capacity)
    (Project.Beck.FreeColumn.source_freeColumn input point supported.capacity supported.overlap nonempty).1 budget

#print axioms direction_supported_exact

end Project.Beck.Execution
