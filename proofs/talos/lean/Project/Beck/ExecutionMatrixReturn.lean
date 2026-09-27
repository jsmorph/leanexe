import Project.Beck.ExecutionMatrixOuterFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixReturn_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (oldNode newNode : FreeNode) (words : Array UInt64)
    (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter) (remaining pageLimit : Nat)
    (valid : current.At middle) (oldOwned : current.OwnsWords middle oldNode #[])
    (newOwned : current.OwnsWords middle newNode words)
    (preserved : original.Frame initial current middle) (oldFresh : FreshFor original oldNode)
    (active : newNode = oldNode ∨ regionsDisjoint oldNode.region newNode.region)
    (budget : OutputBudget middle current remaining pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → finalHeap.OwnsWords final newNode words →
      original.Frame initial finalHeap final → OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ frame, frame.values = [.i64 newNode.root, .i64 newNode.root] → Q (.Fallthrough final frame)) :
    wp Project.Beck.«module» (func19.drop 54) Q middle
      (matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer input.categories newNode.root oldNode.root saved tail after) env := by
  have nonzero : oldNode.root ≠ 0 := by
    intro zero
    have root := oldOwned.buffer.rootBound
    rw [zero] at root
    contradiction
  have newNonzero : newNode.root ≠ 0 := by
    intro zero
    have root := newOwned.buffer.rootBound
    rw [zero] at root
    contradiction
  by_cases same : oldNode.root = newNode.root
  · simp only [func19, List.drop, matrixOuterFrame, matrixPlainFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix,
      matrixOuterSaved, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    repeat' ((try wp_fixed_frame [nonzero, newNonzero, same, List.take, List.drop, List.append_nil]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [nonzero, newNonzero, same, List.take, List.drop, List.append_nil]
    exact next middle current valid newOwned preserved budget _ rfl
  · have separated : regionsDisjoint oldNode.region newNode.region := by
      rcases active with rfl | separated
      · exact (same rfl).elim
      · exact separated
    have call := releaseWords_budget env initial middle original current oldNode #[] remaining pageLimit
      valid oldOwned preserved oldFresh budget
    simp only [func19, List.drop, matrixOuterFrame, matrixPlainFrame, matrixParams, matrixPrefix, matrixTail, matrixSuffix,
      matrixOuterSaved, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    repeat' ((try wp_fixed_frame [nonzero, newNonzero, same, List.take, List.drop, List.append_nil]) <;>
      (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame [nonzero, newNonzero, same, List.take, List.drop, List.append_nil]
    refine wp_call_tw call ?_
    rintro final values ⟨rfl, rfl, finalValid, finalFrame, finalBudget⟩
    have retained := newOwned.released oldNode oldOwned.buffer.rootBound
      (by have := oldOwned.buffer.addressBound; omega) (regionsDisjoint_symm separated)
    wp_fixed_frame [List.take, List.drop, List.append_nil]
    exact next _ _ finalValid retained finalFrame finalBudget _ rfl

#print axioms matrixReturn_exact

end Project.Beck.Execution
