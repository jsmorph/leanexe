import Project.Beck.ExecutionMembershipState
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.FixedArrayLengthRead

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def membershipPreparedSaved (position categories category : Nat) (wordsOwner wordsPointer rowPointer internal : UInt64)
    (saved : MemberSetSaved) (index : Fin 24) : Value :=
  match index.val with
  | 7 => .i64 wordsOwner
  | 8 => .i64 wordsPointer
  | 9 => .i64 (position + 1).toUInt64
  | 10 => .i64 categories.toUInt64
  | 11 => .i64 rowPointer
  | 12 => .i64 category.toUInt64
  | _ => membershipSaved internal saved index

def membershipPreparedFrame (count position categories category size : Nat)
    (wordsOwner wordsPointer rowPointer internal : UInt64) (saved : MemberSetSaved) (tail : MembershipTail) : Locals :=
  { params := membershipParams count.toUInt64 wordsOwner wordsPointer position.toUInt64 categories.toUInt64 rowPointer rowPointer
    locals := memberSetPrefix (membershipPreparedSaved position categories category wordsOwner wordsPointer rowPointer internal saved) ++
      [.i64 rowPointer, .i64 category.toUInt64, .i64 size.toUInt64, .i64 (tail 3),
        .i64 (tail 4), .i64 (tail 5), .i64 1, .i64 (tail 7), .i64 (tail 8), .i64 (tail 9),
        .i64 (tail 10), .i64 (tail 11), .i64 (tail 12), .i64 (tail 13), .i64 (tail 14)]
    values := [.i32 (if category.toUInt64 < size.toUInt64 then 1 else 0)] }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem membershipPrepare_exact (env : HostEnv Unit) (initial : Store Unit)
    (count position categories category : Nat) (wordsOwner wordsPointer rowPointer internal : UInt64)
    (saved : MemberSetSaved) (tail : MembershipTail) (row : Array UInt64)
    (represented : UInt64Array.At initial rowPointer row) (positionBound : position + 1 < UInt64.size)
    (categoryRead : saved 6 = .i64 category.toUInt64)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (membershipPreparedFrame count position categories category row.size wordsOwner wordsPointer rowPointer internal saved tail) env) :
    wp Project.Beck.«module» (membershipFresh.take 35 ++ rest) Q initial
      (membershipFrame count position categories wordsOwner wordsPointer rowPointer internal saved tail) env := by
  have guard : ¬UInt64.ofNat position + 1 < UInt64.ofNat position := CheckedNatAdd.guard_of_fits position 1 positionBound
  have addition : UInt64.ofNat position + 1 = UInt64.ofNat (position + 1) := (UInt64.ofNat_add position 1).symm
  have headerBound : rowPointer.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [represented.pointerAddress_toNat]
    have := represented.2.1
    omega
  simp only [membershipFresh, membershipInRange, membershipBody, func2, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.take, List.cons_append, List.nil_append,
    membershipFrame, membershipParams, memberSetPrefix, membershipSaved, membershipTail,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, categoryRead]
  wp_fixed_frame [guard]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_fixed_frame [List.take, List.drop, List.append_nil, addition]
  rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
  simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero,
    Nat.not_lt.mpr headerBound, reduceIte, represented.lengthRead, or_false, false_or]
  simpa only [membershipPreparedFrame, membershipParams, memberSetPrefix, membershipPreparedSaved,
    membershipSaved, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte,
    List.cons_append, List.nil_append, categoryRead, Nat.toUInt64, or_false, false_or] using next

#print axioms membershipPrepare_exact

end Project.Beck.Execution
