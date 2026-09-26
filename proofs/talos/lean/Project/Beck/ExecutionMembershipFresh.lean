import Project.Beck.ExecutionMembershipFinish
import Project.Beck.ExecutionDetState

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 2048 in
theorem membership_cleanup_shape : membershipFresh.drop 39 = membershipRelease ++ membershipFresh.drop 54 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem membershipFresh_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (count position categories category : Nat) (wordsOwner wordsPointer internal : UInt64) (oldNode : FreeNode)
    (saved : MemberSetSaved) (tail : MembershipTail) (row : Array UInt64) (remaining pageLimit : Nat)
    (valid : current.At middle) (owned : current.OwnsWords middle oldNode row)
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (inputDifferent : oldNode.root ≠ wordsOwner) (ownerNonzero : wordsOwner ≠ 0)
    (bound : row.size ≤ 56) (inside : category < row.size) (positionBound : position + 1 < UInt64.size)
    (categoryRead : saved 6 = .i64 category.toUInt64)
    (budget : OutputBudget middle current (48 + 8 * (row.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final →
      finalHeap.OwnsWords final node (row.set! category 1) →
      original.Frame initial finalHeap final → FreshFor original node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail, Q (.Fallthrough final
        (membershipFrame count (position + 1) categories wordsOwner wordsPointer node.root node.root saved tail))) :
    wp Project.Beck.«module» membershipFresh Q middle
      (membershipFrame (count + 1) position categories wordsOwner wordsPointer oldNode.root internal saved tail) env := by
  let need := UInt64.ofNat (8 * (row.size + 1))
  have needWord : need.toNat = 8 * (row.size + 1) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space : takeFirstFitFrom 0 need current.nodes = none →
      current.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun h => ((budget.bump need (by rw [needWord]; omega)) h).1.le
  have separated := owned.allocation_disjoint need space
  have fresh := allocated_fresh original current initial middle preserved need space
  have ownerDifferent : wordsOwner ≠ internal := by
    rcases active with zero | ⟨equal, _⟩
    · simpa only [zero] using ownerNonzero
    · simpa only [equal] using inputDifferent.symm
  rw [← List.take_append_drop 35 membershipFresh]
  apply membershipPrepare_exact env middle (count + 1) position categories category wordsOwner wordsPointer oldNode.root internal
    saved tail row owned.buffer.values positionBound categoryRead
  apply membershipAllocate_exact env middle current (count + 1) position categories category wordsOwner wordsPointer oldNode.root internal
    saved tail row remaining pageLimit owned.buffer.values (ownedWords_protects owned) valid bound inside budget
  intro allocated
  dsimp only
  intro allocatedValid newOwned allocationFrame allocatedBudget previous cursor capacity after
  rw [membership_cleanup_shape]
  apply membershipCleanup_exact env initial allocated original (current.allocate need) _ oldNode
    (allocatedNode current.top need current.nodes) row (row.set! category 1) internal wordsOwner remaining pageLimit
    allocatedValid (allocationFrame.ownsWords allocatedValid owned) newOwned
    (preserved.trans allocationFrame) active separated inputDifferent allocatedBudget
  all_goals first
    | (solve | simp only [membershipAllocatedFrame, memberSetFrame, membershipParams, memberSetPrefix,
        membershipPreparedSaved, membershipSaved, Locals.get, List.cons_append, List.nil_append, List.length,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
        Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, or_false, false_or, reduceIte, need])
    | skip
  intro final finalHeap finalValid finalOwned finalFrame finalBudget
  apply membershipFinish_exact env final count position categories category row.size wordsOwner wordsPointer oldNode.root internal
    saved tail (allocatedNode current.top need current.nodes).root need previous cursor capacity after ownerNonzero ownerDifferent
  exact next final finalHeap _ finalValid finalOwned finalFrame fresh finalBudget

#print axioms membershipFresh_exact

end Project.Beck.Execution
