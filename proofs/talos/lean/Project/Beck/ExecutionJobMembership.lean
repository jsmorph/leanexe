import Project.Beck.ExecutionJobPrepareRow

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def jobMembershipFailed : Wasm.Program :=
  match (jobEligible[78]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

set_option maxRecDepth 2048 in
theorem job_membership_shape : jobEligible.drop 58 =
    [.localGet 52, .localSet 24, .localGet 24, .localSet 25, .localGet 24, .localSet 26,
      .localGet 18, .localGet 19, .localGet 20, .localGet 21, .localGet 22, .localGet 25, .localGet 26,
      .call 2, .localSet 29, .localSet 28, .localSet 27, .localGet 27, .constI64 0, .eqI64,
      .iff 0 0 jobMembershipFailed jobAccepted] := rfl

def jobReplicatedTail (categories : Nat) (root padding55 padding56 need previous current capacity next : UInt64)
    (after : JobAfter) (index : Fin 17) : UInt64 :=
  match index.val with
  | 0 | 2 => categories.toUInt64
  | 1 | 11 => root
  | 3 => 0
  | 4 => padding55
  | 5 => padding56
  | 6 => need
  | 7 => previous
  | 8 => current
  | 9 => capacity
  | 10 => next
  | 12 => after 0
  | 13 => after 1
  | 14 => after 2
  | 15 => after 3
  | _ => after 4

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem jobMembershipCall_exact (env : HostEnv Unit) (initial middle : Store Unit) (original current : Heap)
    (count categories members : Nat) (wordsPointer internal : UInt64) (oldNode zeroNode : FreeNode)
    (state : ParseState) (words row : Array UInt64) (saved : JobSaved)
    (padding55 padding56 need previous cursor capacity after : UInt64) (suffix : JobAfter) (remaining pageLimit : Nat)
    (valid : current.At middle) (owned : current.OwnsWords middle oldNode state.incidence)
    (zeroOwned : current.OwnsWords middle zeroNode (Array.replicate categories 0))
    (wordsAt : UInt64Array.At middle wordsPointer words)
    (wordsProtected : current.Protects wordsPointer.toNat (wordsPointer.toNat + 8 * (words.size + 1)))
    (preserved : original.Frame initial current middle)
    (active : internal = 0 ∨ internal = oldNode.root ∧ FreshFor original oldNode)
    (inputDifferent : oldNode.root ≠ wordsPointer) (zeroDifferent : zeroNode.root ≠ wordsPointer) (ownerNonzero : wordsPointer ≠ 0)
    (memberBound : members ≤ 8) (categoryBound : categories ≤ 8)
    (inputBound : state.position + 1 + members ≤ words.size) (overlapFit : state.overlap < UInt64.size)
    (accepted : readMemberships members words (state.position + 1) categories (Array.replicate categories 0) = some row)
    (bound : state.incidence.size + row.size ≤ 56)
    (budget : OutputBudget middle current (membershipBytes members categories +
      (48 + 8 * (state.incidence.size + row.size + 1) + remaining)) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final → finalHeap.OwnsWords final node (state.incidence ++ row) →
      original.Frame initial finalHeap final → FreshFor original node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ saved tail, Q (.Fallthrough final
        (jobFrame count categories wordsPointer node.root node.root (jobNextState state members row) saved tail))) :
    wp Project.Beck.«module» (jobEligible.drop 58) Q middle
      (jobReplicateFrame (jobParams (count + 1) categories wordsPointer oldNode.root state)
        (jobPreparedSaved categories members wordsPointer internal state saved) categories zeroNode.root categories.toUInt64 0
        padding55 padding56 need previous cursor capacity after zeroNode.root suffix) env := by
  have positionFit : state.position + 1 + members < UInt64.size := inputBound.trans_lt wordsAt.size_lt
  have call := readMemberships_exact env middle current members (state.position + 1) categories wordsPointer zeroNode
    words (Array.replicate categories 0) row (48 + 8 * (state.incidence.size + row.size + 1) + remaining) pageLimit
    valid zeroOwned wordsAt wordsProtected zeroDifferent ownerNonzero memberBound categoryBound (by simp) inputBound accepted budget
  rw [job_membership_shape]
  generalize acceptedEq : jobAccepted = acceptedCode
  simp only [jobReplicateFrame, jobParams, jobPreparedSaved, jobSaved, jobPrefix,
    List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
    or_false, false_or, reduceIte]
  wp_fixed_frame
  apply wp_call_tw call
  rintro final values ⟨finalHeap, rowNode, rfl, finalValid, rowOwned, memberFrame, finalBudget⟩
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  rw [← acceptedEq]
  apply jobReadFrame_wp env final _ (count + 1) categories members wordsPointer oldNode.root rowNode.root internal state
    (jobReplicatedTail categories zeroNode.root padding55 padding56 need previous cursor capacity after suffix)
  all_goals first | rfl | (solve | intro index; fin_cases index <;> rfl) | skip
  intro finalSaved finalTail
  apply jobAccepted_exact env initial final original finalHeap count categories members wordsPointer rowNode.root internal oldNode state row
    finalSaved finalTail remaining pageLimit finalValid (memberFrame.ownsWords finalValid owned) rowOwned.buffer.values
    (ownedWords_protects rowOwned) (preserved.trans memberFrame) active inputDifferent ownerNonzero bound positionFit overlapFit finalBudget
  intro result resultHeap resultNode resultValid resultOwned resultFrame fresh resultBudget resultSaved resultTail
  simpa only [jobFrame, List.take, List.drop, List.append_nil, wp_nil] using
    next result resultHeap resultNode resultValid resultOwned resultFrame fresh resultBudget resultSaved resultTail

#print axioms jobMembershipCall_exact

end Project.Beck.Execution
