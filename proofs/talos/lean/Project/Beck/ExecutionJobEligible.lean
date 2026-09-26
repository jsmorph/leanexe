import Project.Beck.ExecutionJobMembership

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def jobStepBytes (members categories incidenceSize rowSize : Nat) : Nat :=
  48 + 8 * (categories + 1) + membershipBytes members categories + 48 + 8 * (incidenceSize + rowSize + 1)

theorem jobStepBytes_bound (members categories incidenceSize rowSize : Nat)
    (memberBound : members ≤ 8) (categoryBound : categories ≤ 8) (sizeBound : incidenceSize + rowSize ≤ 48) :
    jobStepBytes members categories incidenceSize rowSize ≤ 1520 := by
  have := membershipBytes_bound members categories memberBound categoryBound
  unfold jobStepBytes
  omega

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem jobEligible_exact {rowOwner : UInt64} (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (count categories members : Nat) (wordsPointer internal : UInt64) (oldNode : FreeNode)
    (state : ParseState) (words row : Array UInt64) (saved : JobSaved) (tail : JobTail) (remaining pageLimit : Nat)
    (valid : current.At middle) (owned : current.OwnsWords middle oldNode state.incidence)
    (wordsAt : UInt64Array.At middle wordsPointer words)
    (wordsProtected : current.Protects wordsPointer.toNat (wordsPointer.toNat + 8 * (words.size + 1)))
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (inputDifferent : oldNode.root ≠ wordsPointer) (ownerNonzero : wordsPointer ≠ 0)
    (memberBound : members ≤ 8) (categoryBound : categories ≤ 8)
    (inputBound : state.position + 1 + members ≤ words.size) (overlapFit : state.overlap < UInt64.size)
    (accepted : readMemberships members words (state.position + 1) categories (Array.replicate categories 0) = some row)
    (bound : state.incidence.size + row.size ≤ 56)
    (budget : OutputBudget middle current (jobStepBytes members categories state.incidence.size row.size + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final → finalHeap.OwnsWords final node (state.incidence ++ row) →
      original.Frame initial finalHeap final → FreshFor original node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail, Q (.Fallthrough final
        (jobFrame count categories wordsPointer node.root node.root (jobNextState state members row) saved tail))) :
    wp Project.Beck.«module» jobEligible Q middle
      (jobCountFrame (rowOwner := rowOwner) (count + 1) categories members wordsPointer oldNode.root internal state saved tail) env := by
  let need := UInt64.ofNat (8 * (categories + 1))
  have needWord : need.toNat = 8 * (categories + 1) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space : takeFirstFitFrom 0 need current.nodes = none →
      current.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun h => ((budget.bump need (by rw [needWord]; unfold jobStepBytes; omega)) h).1.le
  have fresh := allocated_fresh current current middle middle (Heap.Frame.refl current middle) need space
  rw [← List.take_append_drop 16 jobEligible]
  apply jobPrepareRow_exact env middle (count + 1) categories members wordsPointer oldNode.root internal state saved tail
  change wp Project.Beck.«module» ((jobEligible.drop 16).take 42 ++ jobEligible.drop 58) Q middle _ env
  apply jobReplicateCapacity_owned env middle current _ (jobPreparedSaved categories members wordsPointer internal state saved) rfl categories
    (tail 1) (tail 2) 0 (tail 4) (tail 5) (tail 6) (tail 7) (tail 8) (tail 9) (tail 10) (tail 11) _
    (membershipBytes members categories + (48 + 8 * (state.incidence.size + row.size + 1) + remaining)) pageLimit valid (by omega)
    (by simpa only [jobStepBytes, Nat.add_assoc] using budget)
  intro allocated
  dsimp only
  intro allocatedValid zeroOwned allocationFrame allocatedBudget previous cursor capacity after
  apply jobMembershipCall_exact env initial allocated original (current.allocate need) count categories members wordsPointer internal oldNode
    (allocatedNode current.top need current.nodes) state words row saved (tail 4) (tail 5) need previous cursor capacity after _ remaining pageLimit
    allocatedValid (allocationFrame.ownsWords allocatedValid owned) zeroOwned (allocationFrame.words wordsProtected wordsAt)
    (allocationFrame.protects _ _ wordsProtected) (preserved.trans allocationFrame) active inputDifferent
    (fresh.pointer_ne wordsPointer words.size wordsProtected (by dsimp only [need]; have := zeroOwned.buffer.capacity; omega) zeroOwned.buffer.rootBound)
    ownerNonzero memberBound categoryBound inputBound overlapFit accepted bound allocatedBudget Q next

#print axioms jobEligible_exact

end Project.Beck.Execution
