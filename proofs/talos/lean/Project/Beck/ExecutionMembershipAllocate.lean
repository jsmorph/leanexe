import Project.Beck.ExecutionMembershipPrepare
import Project.Beck.ExecutionMembershipCleanup

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def membershipAllocatedFrame (count position categories category size : Nat)
    (wordsOwner wordsPointer rowPointer internal : UInt64) (saved : MemberSetSaved) (tail : MembershipTail)
    (root need previous current capacity next : UInt64) : Locals :=
  memberSetFrame
    (membershipParams count.toUInt64 wordsOwner wordsPointer position.toUInt64 categories.toUInt64 rowPointer rowPointer)
    (fun k => if k.val = 14 ∨ k.val = 15 then .i64 root else
      membershipPreparedSaved position categories category wordsOwner wordsPointer rowPointer internal saved k)
    rowPointer category size root size.toUInt64 1 (tail 7) (tail 8) need previous current capacity next root

set_option maxRecDepth 2048 in
theorem membership_allocate_shape : membershipFresh.drop 35 =
    [.iff 0 1 membershipSetBranch [.unreachable] [] [.i64], .localSet 21, .localGet 21, .localSet 22] ++
      membershipFresh.drop 39 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem membershipAllocate_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (count position categories category : Nat) (wordsOwner wordsPointer rowPointer internal : UInt64)
    (saved : MemberSetSaved) (tail : MembershipTail) (row : Array UInt64) (remaining pageLimit : Nat)
    (represented : UInt64Array.At initial rowPointer row)
    (protects : heap.Protects rowPointer.toNat (rowPointer.toNat + 8 * (row.size + 1)))
    (valid : heap.At initial) (bound : row.size ≤ 56) (inside : category < row.size)
    (budget : OutputBudget initial heap (48 + 8 * (row.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let need := UInt64.ofNat (8 * (row.size + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final node (row.set! category 1) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» (membershipFresh.drop 39) Q final
        (membershipAllocatedFrame count position categories category row.size wordsOwner wordsPointer rowPointer internal saved tail
          node.root need previous current capacity next) env) :
    wp Project.Beck.«module» (membershipFresh.drop 35) Q initial
      (membershipPreparedFrame count position categories category row.size wordsOwner wordsPointer rowPointer internal saved tail) env := by
  have sizeFit : row.size < UInt64.size := represented.size_lt
  have categoryFit : category < UInt64.size := lt_trans inside sizeFit
  have guard : category.toUInt64 < row.size.toUInt64 := by
    change (UInt64.ofNat category).toNat < (UInt64.ofNat row.size).toNat
    simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt sizeFit, Nat.mod_eq_of_lt categoryFit]
    exact inside
  rw [membership_allocate_shape]
  generalize restEq : membershipFresh.drop 39 = rest
  simp only [List.cons_append, List.nil_append, membershipPreparedFrame, guard, reduceIte]
  simp only [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by decide)]
  change wp Project.Beck.«module»
    ([.localGet 33, .constI64 1, .mulI64, .localSet 34] ++ membershipSetBranch.drop 4) _ _ _ _
  simp only [List.cons_append, List.nil_append, memberSetPrefix, membershipParams]
  wp_fixed_frame [UInt64.mul_one]
  rw [← List.append_nil (membershipSetBranch.drop 4)]
  apply membershipSetCapacity_owned env initial heap _
    (membershipPreparedSaved position categories category wordsOwner wordsPointer rowPointer internal saved) rfl
    rowPointer row category (tail 4) (tail 5) 1 (tail 7) (tail 8) (tail 9)
    (tail 10) (tail 11) (tail 12) (tail 13) (tail 14) remaining pageLimit
    represented protects valid bound inside budget
  intro final
  dsimp only
  intro finalValid owned frame finalBudget previous current capacity after
  simp only [wp_nil, memberSetFrame, memberSetPrefix, membershipParams, List.take, List.drop,
    List.cons_append, List.nil_append, List.append_nil]
  wp_fixed_frame
  rw [← restEq]
  simpa only [membershipAllocatedFrame, memberSetFrame, memberSetPrefix, membershipParams,
    List.cons_append, List.nil_append, Locals.set, List.length, List.set, Nat.reduceLT,
    Nat.reduceSub, Nat.reduceAdd, reduceIte, allocatedNode, Nat.toUInt64,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or] using
    next final finalValid owned frame finalBudget previous current capacity after

#print axioms membershipAllocate_exact

end Project.Beck.Execution
