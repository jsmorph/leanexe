import Project.Beck.ExecutionMembershipLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem readMemberships_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (count position categories : Nat) (wordsPointer : UInt64) (node : FreeNode)
    (words row out : Array UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (owned : heap.OwnsWords initial node row)
    (wordsAt : UInt64Array.At initial wordsPointer words)
    (wordsProtected : heap.Protects wordsPointer.toNat (wordsPointer.toNat + 8 * (words.size + 1)))
    (inputDifferent : node.root ≠ wordsPointer) (ownerNonzero : wordsPointer ≠ 0)
    (countBound : count ≤ 8) (categoryBound : categories ≤ 8)
    (rowSize : row.size = categories) (inputBound : position + count ≤ words.size)
    (accepted : readMemberships count words position categories row = some out)
    (budget : OutputBudget initial heap (membershipBytes count categories + remaining) pageLimit Project.Beck.«module») :
    TerminatesWith env Project.Beck.«module» 2 initial
      (membershipParams count.toUInt64 wordsPointer wordsPointer position.toUInt64 categories.toUInt64 node.root node.root).reverse
      (fun final values => ∃ finalHeap finalNode,
        values = [.i64 finalNode.root, .i64 finalNode.root, .i64 1] ∧
        finalHeap.At final ∧ finalHeap.OwnsWords final finalNode out ∧ heap.Frame initial finalHeap final ∧
        OutputBudget final finalHeap remaining pageLimit Project.Beck.«module») := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_
  change wp Project.Beck.«module» func2 _ initial
    { params := membershipParams count.toUInt64 wordsPointer wordsPointer position.toUInt64 categories.toUInt64 node.root node.root
      locals := List.replicate 39 (.i64 0) } env
  simp only [func2, membershipParams]
  wp_fixed_frame
  change wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 membershipBody]] ++ func2.drop 7) _ initial
    (membershipFrame count position categories wordsPointer wordsPointer node.root 0 (fun _ => .i64 0) (fun _ => 0)) env
  apply membershipLoop_exact env initial heap count position categories wordsPointer node _ _ words row out remaining pageLimit
    valid owned wordsAt wordsProtected inputDifferent ownerNonzero countBound categoryBound rowSize inputBound accepted budget
  intro final finalHeap finalNode finalValid finalOwned finalFrame finalBudget internal saved tail
  simp only [func2, List.drop, membershipFrame, membershipParams, memberSetPrefix, membershipSaved, membershipTail,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte,
    List.cons_append, List.nil_append]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  wp_fixed_frame [List.take, List.drop, List.append_nil, func2Def]
  exact ⟨finalHeap, finalNode, rfl, finalValid, finalOwned, finalFrame, finalBudget⟩

#print axioms readMemberships_exact

end Project.Beck.Execution
