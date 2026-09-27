import Project.Beck.ExecutionMatrixSelected
import Project.Beck.ExecutionMatrixOuterPrepare
import Project.Beck.ExecutionMatrixOuterFinish

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
theorem matrix_outer_step_shape : matrixBody.drop 4 = (matrixBody.drop 4).take 39 ++
    [.iff 0 0 matrixSelected [.localGet 15, .localSet 46, .localGet 16, .localSet 47]] ++ matrixBody.drop 44 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem matrixOuterStep_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (category : Nat) (node : FreeNode) (owner : UInt64) (base : Array UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) (remaining pageLimit : Nat)
    (valid : heap.At initial) (owned : heap.OwnsWords initial node base)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8) (categoryBound : category < input.categories)
    (overlap : input.overlap ≤ 8) (bound : base.size + input.jobs ≤ 48)
    (budget : OutputBudget initial heap (448 * input.jobs + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap finalNode, finalHeap.At final →
      finalHeap.OwnsWords final finalNode (if input.overlap < liveCount input point category then
        base ++ (ProtectedMatrix.row input point category).toArray else base) →
      heap.Frame initial finalHeap final → (finalNode = node ∨ FreshFor heap finalNode) →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail after, Q (.Break 0 final
        (matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer (category + 1) finalNode.root owner saved tail after))) :
    wp Project.Beck.«module» (matrixBody.drop 4) Q initial
      (matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer category node.root owner saved tail after) env := by
  rw [matrix_outer_step_shape, List.append_assoc]
  apply matrixOuterPrepare_exact env initial input point inputOwner inputPointer pointOwner pointPointer category node.root owner
    saved tail after pointArray inputArray pointSize inputSize jobs categories categoryBound overlap
  simp only [List.cons_append, List.nil_append]
  refine wp_iff_cons rfl ?_
  by_cases selected : input.overlap < liveCount input point category
  · simp only [selected, reduceIte, ne_eq, show (1 : UInt32) ≠ 0 by decide, not_false_eq_true] 
    change wp Project.Beck.«module» (matrixSelected ++ []) _ initial _ env
    apply matrixSelected_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer category node owner base
      _ tail after remaining pageLimit valid owned pointArray pointProtected inputArray inputProtected
      pointSize inputSize jobs categories categoryBound bound budget rfl rfl rfl rfl rfl rfl rfl
    intro final finalHeap finalNode finalValid finalOwned finalFrame finalActive finalBudget finalSaved finalTail finalAfter
    rw [wp_nil]
    change wp Project.Beck.«module» (matrixBody.drop 44) Q final
      (matrixBranchFrame input point inputOwner inputPointer pointOwner pointPointer category finalNode.root owner finalSaved finalTail finalAfter) env
    apply matrixOuterFinish_exact env final input point inputOwner inputPointer pointOwner pointPointer category finalNode.root owner
      finalSaved finalTail finalAfter (finalFrame.words pointProtected pointArray) (finalFrame.words inputProtected inputArray)
      pointSize inputSize jobs categories categoryBound
    exact next final finalHeap finalNode finalValid (by simpa only [selected, reduceIte] using finalOwned)
      finalFrame finalActive finalBudget
  · simp only [selected, reduceIte, ne_eq, not_true_eq_false]
    simp only [matrixPlainFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix,
      matrixPreparedSaved, matrixOuterSaved, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    wp_fixed_frame [List.take, List.drop, List.append_nil]
    have finish := matrixOuterFinish_exact env initial input point inputOwner inputPointer pointOwner pointPointer category node.root owner
      (matrixPreparedSaved input point inputOwner inputPointer pointOwner pointPointer category node.root owner saved) tail after
      pointArray inputArray pointSize inputSize jobs categories categoryBound Q
      (next initial heap node valid (by simpa only [selected, reduceIte] using owned)
        (Heap.Frame.refl heap initial) (Or.inl rfl) (budget.mono (by omega)))
    simpa only [matrixBranchFrame, matrixPlainFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix,
      matrixBranchSaved, matrixPreparedSaved, matrixOuterSaved, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte] using finish

#print axioms matrixOuterStep_exact

end Project.Beck.Execution
