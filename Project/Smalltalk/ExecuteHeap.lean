import Project.Smalltalk.InstructionHeap
import Project.Smalltalk.LiteralHeap

namespace Project.Smalltalk.ExecuteHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.Reachability Project.Smalltalk.InstructionHeap
open Project.Smalltalk.LiteralHeap Project.Smalltalk.PushReservation

def Covered (op : UInt64) : Prop := op ≤ 9 ∨ op = 14 ∨ op = 15

theorem execute_integer_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5) (a b : UInt64) :
    Heap.Valid (execute p s 0 a b) cap := by
  simpa [execute] using literal_scalar_valid valid phase activation (tag := 1) (a := a) (b := 0) (Or.inl rfl)

theorem execute_canonical_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5) (a b : UInt64) :
    Heap.Valid (execute p s 1 a b) cap := by
  change Heap.Valid (if a ≤ 2 then push s (a + 1) else fail s 10) cap
  split
  · rename_i bound
    exact (push_correct valid phase activation (canonical_live s a bound)).1
  · exact Heap.fail_valid valid 10

theorem execute_block_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5) (a b : UInt64) :
    Heap.Valid (execute p s 6 a b) cap := by
  change Heap.Valid (if a == 0 || a > read p 1 then fail s 10 else
    if methodAt p a 1 != 0 || methodAt p a 0 != methodAt p (field s (read s 2) 2) 0 then fail s 10
    else literal s 6 a (read s 2)) cap
  split
  · exact Heap.fail_valid valid 10
  · split
    · exact Heap.fail_valid valid 10
    · exact literal_block_valid valid phase activation

theorem execute_class_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5) (a b : UInt64) :
    Heap.Valid (execute p s 7 a b) cap := by
  change Heap.Valid (if a == 0 || a > read p 0 then fail s 10 else literal s 8 a (classAt p a 1)) cap
  split
  · exact Heap.fail_valid valid 10
  · exact literal_scalar_valid valid phase activation (Or.inr rfl)

theorem execute_dup_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5) (a b : UInt64) :
    Heap.Valid (execute p s 8 a b) cap := by
  let stack := field s (read s 2) 7
  change Heap.Valid (if kind s stack != 7 then fail s 4 else push s (field s stack 2)) cap
  by_cases cell : kind s stack = 7
  · simp only [show (kind s stack != 7) = false by rw [cell]; rfl, Bool.false_eq_true, ite_false]
    exact (push_correct valid phase activation (top_live valid.1 activation cell)).1
  · simp only [show (kind s stack != 7) = true from bne_iff_ne.mpr cell, ite_true]
    exact Heap.fail_valid valid 4

theorem execute_jump_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (activation : kind s (read s 2) = 5) (a b : UInt64) : Heap.Valid (execute p s 14 a b) cap := by
  change Heap.Valid (if a ≥ read p 2 then fail s 10 else write s (address (read s 2) + 3) a) cap
  split
  · exact Heap.fail_valid valid 10
  · exact jump_valid valid activation a

theorem execute_covered_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5)
    (op a b : UInt64) (covered : Covered op) : Heap.Valid (execute p s op a b) cap := by
  rcases covered with small | rfl | rfl
  · have nbound := UInt64.le_iff_toNat_le.mp small
    change op.toNat ≤ 9 at nbound
    have cases : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 ∨ op = 9 := by
      have ns : op.toNat = 0 ∨ op.toNat = 1 ∨ op.toNat = 2 ∨ op.toNat = 3 ∨ op.toNat = 4 ∨
          op.toNat = 5 ∨ op.toNat = 6 ∨ op.toNat = 7 ∨ op.toNat = 8 ∨ op.toNat = 9 := by omega
      simpa only [← UInt64.toNat_inj, UInt64.reduceToNat] using ns
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact execute_integer_valid valid phase activation a b
    · exact execute_canonical_valid valid phase activation a b
    · simpa [execute] using accessLocal_valid valid phase activation 2 a b
    · simpa [execute] using accessLocal_valid valid phase activation 3 a b
    · simpa [execute] using accessField_valid valid phase activation 4 a
    · simpa [execute] using accessField_valid valid phase activation 5 a
    · exact execute_block_valid valid phase activation a b
    · exact execute_class_valid valid phase activation a b
    · exact execute_dup_valid valid phase activation a b
    · simpa [execute] using StackWrite.pop_valid valid activation
  · exact execute_jump_valid valid activation a b
  · simpa [execute] using branch_valid valid activation a

theorem step_covered_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (covered : Covered (codeAt p (field s (read s 2) 3) 0)) : Heap.Valid (step p s) cap := by
  by_cases running : read s 0 = 0
  · have phase : read s 0 ≠ 4 := by rw [running]; decide
    dsimp only [step]
    simp only [running, bne_self_eq_false, Bool.false_eq_true, ite_false]
    by_cases activation : kind s (read s 2) = 5
    · simp only [show (kind s (read s 2) != 5) = false by rw [activation]; rfl,
        Bool.false_eq_true, ite_false]
      split
      · exact Heap.fail_valid valid 1
      · split
        · exact Heap.fail_valid valid 10
        · exact execute_covered_valid valid phase activation _ _ _ covered
    · simp only [show (kind s (read s 2) != 5) = true from bne_iff_ne.mpr activation, ite_true]
      exact Heap.fail_valid valid 1
  · simp only [step, show (read s 0 != 0) = true from bne_iff_ne.mpr running, ite_true]
    exact valid

end Project.Smalltalk.ExecuteHeap
