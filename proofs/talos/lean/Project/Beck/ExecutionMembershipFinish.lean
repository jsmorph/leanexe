import Project.Beck.ExecutionMembershipAllocate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def membershipAllocatedTail (category size : Nat) (rowPointer root need previous current capacity next : UInt64)
    (tail : MembershipTail) (index : Fin 15) : UInt64 :=
  match index.val with
  | 0 => rowPointer
  | 1 => category.toUInt64
  | 2 | 3 | 5 => size.toUInt64
  | 4 | 14 => root
  | 6 => 1
  | 7 => tail 7
  | 8 => tail 8
  | 9 => need
  | 10 => previous
  | 11 => current
  | 12 => capacity
  | _ => next

theorem membershipFrame_post (store : Store Unit) (frame : Locals) (count position categories : Nat)
    (wordsOwner wordsPointer rowPointer internal : UInt64) (tail : MembershipTail)
    (Q : Assertion Unit)
    (next : ∀ saved tail, Q (.Fallthrough store
      (membershipFrame count position categories wordsOwner wordsPointer rowPointer internal saved tail)))
    (params : frame.params = membershipParams count.toUInt64 wordsOwner wordsPointer position.toUInt64 categories.toUInt64 rowPointer rowPointer)
    (locals : frame.locals.length = 39) (values : frame.values = [])
    (r7 : frame.get 7 = some (.i64 internal)) (r8 : frame.get 8 = some (.i64 0)) (r12 : frame.get 12 = some (.i64 0))
    (tailReads : ∀ index : Fin 15, frame.get (index.val + 31) = some (.i64 (tail index))) :
    Q (.Fallthrough store frame) := by
  rw [membershipFrame_reconstruct frame count position categories wordsOwner wordsPointer rowPointer internal tail
    params locals values r7 r8 r12 tailReads]
  exact next _ tail

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem membershipFinish_exact (env : HostEnv Unit) (initial : Store Unit)
    (count position categories category size : Nat) (wordsOwner wordsPointer rowPointer internal : UInt64)
    (saved : MemberSetSaved) (tail : MembershipTail) (root need previous current capacity after : UInt64)
    (ownerNonzero : wordsOwner ≠ 0) (ownerDifferent : wordsOwner ≠ internal)
    (Q : Assertion Unit)
    (next : ∀ saved tail, Q (.Fallthrough initial
      (membershipFrame count (position + 1) categories wordsOwner wordsPointer root root saved tail))) :
    wp Project.Beck.«module» (membershipFresh.drop 54) Q initial
      (membershipAllocatedFrame (count + 1) position categories category size wordsOwner wordsPointer rowPointer internal saved tail
        root need previous current capacity after) env := by
  have decrement : (count + 1).toUInt64 - 1 = count.toUInt64 := by
    rw [Nat.toUInt64, UInt64.ofNat_add]
    exact UInt64.add_sub_cancel _ _
  simp only [membershipFresh, membershipInRange, membershipBody, func2, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.drop, membershipAllocatedFrame, memberSetFrame,
    membershipPreparedSaved, membershipSaved, memberSetPrefix, membershipParams,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, or_false, false_or, reduceIte,
    List.cons_append, List.nil_append]
  repeat' ((try wp_fixed_frame [ownerNonzero, ownerDifferent, List.take, List.drop, List.append_nil, decrement]) <;>
    (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  wp_fixed_frame [ownerNonzero, ownerDifferent, List.take, List.drop, List.append_nil, decrement]
  apply membershipFrame_post initial _ count (position + 1) categories wordsOwner wordsPointer root root
    (membershipAllocatedTail category size rowPointer root need previous current capacity after tail) Q next
  all_goals first | rfl | (intro index; fin_cases index <;> rfl)

#print axioms membershipFinish_exact

end Project.Beck.Execution
