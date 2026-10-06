import Project.Smalltalk.StackWrite
import Project.Smalltalk.PushReservation

namespace Project.Smalltalk.InstructionHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.HeapWrite Project.Smalltalk.Reachability
open Project.Smalltalk.StackPush Project.Smalltalk.PushReservation Project.Smalltalk.FrameHeap

theorem accessLocal_valid {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5) (op index depth : UInt64) :
    Heap.Valid (accessLocal s op index depth) cap := by
  let slot := localSlot s (read s 2) index depth
  have live := localSlot_live valid.1 (root_live s 2 (Or.inl rfl)) index depth
  have cell : slot = 0 ∨ kind s slot = 7 := by
    by_cases zero : slot = 0
    · exact Or.inl zero
    · exact Or.inr (localSlot_tag zero)
  change Heap.Valid (if op == 2 then loadSlot s slot else storeSlot s slot) cap
  split
  · exact loadSlot_valid valid phase activation live cell
  · exact StackWrite.storeSlot_valid valid activation cell

theorem accessField_valid {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5) (op index : UInt64) :
    Heap.Valid (accessField s op index) cap := by
  let slot := fieldSlot s index
  have live := fieldSlot_live valid.1 index
  have cell : slot = 0 ∨ kind s slot = 7 := by
    by_cases zero : slot = 0
    · exact Or.inl zero
    · exact Or.inr (fieldSlot_tag zero)
  change Heap.Valid (if op == 4 then loadSlot s slot else storeSlot s slot) cap
  split
  · exact loadSlot_valid valid phase activation live cell
  · exact StackWrite.storeSlot_valid valid activation cell

theorem jump_valid {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (activation : kind s (read s 2) = 5) (pc : UInt64) :
    Heap.Valid (write s (address (read s 2) + 3) pc) cap := by
  have current := current_facts valid.1 activation
  exact write_cell_valid valid current.1 (by rw [current.2.1]; decide)
    (show (3 : UInt64).toNat < 8 by decide) (by decide) (activation_pc_reference current.2.1)

theorem branch_valid {p s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (activation : kind s (read s 2) = 5) (target : UInt64) : Heap.Valid (branch p s target) cap := by
  have current := current_facts valid.1 activation
  let act := read s 2
  let stack := field s act 7
  let value := if kind s stack == 7 then field s stack 2 else 0
  let rest := if kind s stack == 7 then field s stack 3 else 0
  change Heap.Valid (if target ≥ read p 2 then fail s 10 else if kind s stack != 7 then fail s 4
    else if value != 2 && value != 3 then fail s 8 else
    write (write s (address act + 7) rest) (address act + 3)
      (if value == 2 then target else field s act 3 + 1)) cap
  by_cases badTarget : target ≥ read p 2
  · simp only [badTarget, ite_true]; exact Heap.fail_valid valid 10
  · simp only [badTarget, ite_false]
    by_cases cell : kind s stack = 7
    · have handle := kind_handle valid.1.1 (by decide) cell
      have tag : field s stack 0 = 7 := (kind_eq_field valid.1.1 handle).symm.trans cell
      have restValue : Value s cap rest := by
        have eq : rest = field s stack 3 := by simp only [rest, cell, BEq.rfl, ite_true]
        rw [eq]
        exact pointer_value valid.1 handle (by rw [tag]; decide) (show (3 : UInt64).toNat < 8 by decide)
          (by rw [tag]; simp [PointerField])
      simp only [show (kind s stack != 7) = false by rw [cell]; rfl, Bool.false_eq_true, ite_false]
      split
      · exact Heap.fail_valid valid 8
      · have written := write_cell_valid valid current.1 (by rw [current.2.1]; decide)
          (show (7 : UInt64).toNat < 8 by decide) (by decide) (fun _ => restValue)
        have tag : field (write s (address act + 7) rest) act 0 = 5 := by
          rw [cell_tag valid.1.1 current.1 (show (7 : UInt64).toNat < 8 by decide) (by decide) current.1]
          exact current.2.1
        exact write_cell_valid written current.1 (by rw [tag]; decide)
          (show (3 : UInt64).toNat < 8 by decide) (by decide) (activation_pc_reference tag)
    · simp only [show (kind s stack != 7) = true from bne_iff_ne.mpr cell, ite_true]
      exact Heap.fail_valid valid 4

theorem top_live {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (activation : kind s (read s 2) = 5) (cell : kind s (field s (read s 2) 7) = 7) :
    Live s (field s (field s (read s 2) 7) 2) := by
  have current := current_facts valid activation
  have reached := live_reached (root_live s 2 (Or.inl rfl)) (by decide) activation
  have stack := pointer_live reached (show (7 : UInt64).toNat < 8 by decide) (by
    rw [current.2.1]; simp [PointerField])
  have stackReach := live_reached stack (by decide) cell
  apply pointer_live stackReach (show (2 : UInt64).toNat < 8 by decide)
  rw [← kind_eq_field valid.1 (reachable_allocated valid stackReach).1, cell]
  simp [PointerField]

theorem canonical_live (s : Array UInt64) (a : UInt64) (bound : a ≤ 2) : Live s (a + 1) := by
  have nbound := UInt64.le_iff_toNat_le.mp bound
  change a.toNat ≤ 2 at nbound
  have cases : a = 0 ∨ a = 1 ∨ a = 2 := by
    have ncases : a.toNat = 0 ∨ a.toNat = 1 ∨ a.toNat = 2 := by omega
    simpa only [← UInt64.toNat_inj, UInt64.reduceToNat] using ncases
  rcases cases with rfl | rfl | rfl <;> exact Or.inr (.root ⟨by decide, by simp⟩)

end Project.Smalltalk.InstructionHeap
