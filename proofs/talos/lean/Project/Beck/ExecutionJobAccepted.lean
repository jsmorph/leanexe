import Project.Beck.ExecutionJobPrepareAppend

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem jobAccepted_exact {rowOwner : UInt64} (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (count categories members : Nat) (wordsPointer rowPointer internal : UInt64) (oldNode : FreeNode)
    (state : ParseState) (row : Array UInt64) (saved : JobSaved) (tail : JobTail) (remaining pageLimit : Nat)
    (valid : current.At middle) (owned : current.OwnsWords middle oldNode state.incidence)
    (rowAt : UInt64Array.At middle rowPointer row)
    (rowProtected : current.Protects rowPointer.toNat (rowPointer.toNat + 8 * (row.size + 1)))
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (inputDifferent : oldNode.root ≠ wordsPointer) (ownerNonzero : wordsPointer ≠ 0)
    (bound : state.incidence.size + row.size ≤ 56)
    (positionFit : state.position + 1 + members < UInt64.size) (overlapFit : state.overlap < UInt64.size)
    (budget : OutputBudget middle current (48 + 8 * (state.incidence.size + row.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final → finalHeap.OwnsWords final node (state.incidence ++ row) →
      original.Frame initial finalHeap final → FreshFor original node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail, Q (.Fallthrough final
        (jobFrame count categories wordsPointer node.root node.root (jobNextState state members row) saved tail))) :
    wp Project.Beck.«module» jobAccepted Q middle
      (jobReadFrame (rowOwner := rowOwner) (count + 1) categories members wordsPointer oldNode.root rowPointer internal state saved tail) env := by
  let need := UInt64.ofNat (8 * (state.incidence.size + row.size + 1))
  have needWord : need.toNat = 8 * (state.incidence.size + row.size + 1) := by dsimp [need]; rw [UInt64.toNat_ofNat']; omega
  have space : takeFirstFitFrom 0 need current.nodes = none →
      current.top.toNat + 48 + need.toNat ≤ 4294967296 :=
    fun h => ((budget.bump need (by rw [needWord]; omega)) h).1.le
  have separated := owned.allocation_disjoint need space
  have fresh := allocated_fresh original current initial middle preserved need space
  have ownerDifferent : wordsPointer ≠ internal := by
    rcases active with zero | ⟨equal, _⟩
    · simpa only [zero] using ownerNonzero
    · simpa only [equal] using inputDifferent.symm
  rw [← List.take_append_drop 41 jobAccepted]
  apply jobPrepareAppend_exact env middle (count + 1) categories members wordsPointer oldNode.root rowPointer internal
    state row saved tail owned.buffer.values rowAt positionFit overlapFit
  change wp Project.Beck.«module» ((jobAccepted.drop 41).take 45 ++ jobAccepted.drop 86) Q middle _ env
  apply jobAppendCapacity_owned env middle current _ (jobSaved internal (jobAppendSaved state members rowPointer saved)) rfl
    oldNode.root rowPointer state.incidence row (tail 7) (tail 8) (tail 9) (tail 10) (tail 11)
    (tail 12) (tail 13) (tail 14) (tail 15) (tail 16) remaining pageLimit
    owned.buffer.values rowAt (ownedWords_protects owned) rowProtected valid bound budget
  intro allocated
  dsimp only
  intro allocatedValid newOwned allocationFrame allocatedBudget previous cursor capacity after
  change wp Project.Beck.«module» ((jobAccepted.drop 86).take 18 ++ ((jobAccepted.drop 104).take 15 ++ jobAccepted.drop 119)) Q allocated _ env
  apply jobInstall_exact env allocated (count + 1) categories wordsPointer internal state (jobNextState state members row)
    (jobAppendSaved state members rowPointer saved) oldNode.root rowPointer state.incidence.size row.size
    (allocatedNode current.top need current.nodes).root (tail 9) (tail 10) need previous cursor capacity after rfl rfl
  apply jobCleanup_exact env initial allocated original (current.allocate need) _ oldNode
    (allocatedNode current.top need current.nodes) state.incidence (state.incidence ++ row) internal wordsPointer remaining pageLimit
    allocatedValid (allocationFrame.ownsWords allocatedValid owned) newOwned (preserved.trans allocationFrame)
    active separated inputDifferent allocatedBudget
  all_goals first
    | (solve | simp only [jobInstalledFrame, jobAppendFrame, jobParams, jobPrefix, jobInstalledSaved, jobSaved,
        Locals.get, List.cons_append, List.nil_append, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
        or_false, false_or, reduceIte, need])
    | skip
  intro final finalHeap finalValid finalOwned finalFrame finalBudget
  apply jobFinish_exact env final count categories wordsPointer internal state (jobNextState state members row)
    (jobAppendSaved state members rowPointer saved) oldNode.root rowPointer state.incidence.size row.size
    (allocatedNode current.top need current.nodes).root (tail 9) (tail 10) need previous cursor capacity after ownerNonzero ownerDifferent
  exact next final finalHeap _ finalValid finalOwned finalFrame fresh finalBudget

#print axioms jobAccepted_exact

end Project.Beck.Execution
