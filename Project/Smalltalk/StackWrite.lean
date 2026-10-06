import Project.Smalltalk.Reachability
import Project.Smalltalk.FrameHeap

namespace Project.Smalltalk.StackWrite
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.Reachability Project.Smalltalk.HeapWrite

theorem pop_valid {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (activation : kind s (read s 2) = 5) : Heap.Valid (pop s) cap := by
  have actHandle := kind_handle valid.1.1 (by decide) activation
  have actTag : field s (read s 2) 0 = 5 := (kind_eq_field valid.1.1 actHandle).symm.trans activation
  let stack := field s (read s 2) 7
  change Heap.Valid (if kind s stack != 7 then fail s 4 else advance s (field s stack 3)) cap
  by_cases cell : kind s stack = 7
  · have handle := kind_handle valid.1.1 (by decide) cell
    have tag : field s stack 0 = 7 := (kind_eq_field valid.1.1 handle).symm.trans cell
    have rest := pointer_value valid.1 handle (by rw [tag]; decide)
      (show (3 : UInt64).toNat < 8 by decide) (by rw [tag]; simp [PointerField])
    simp only [show (kind s stack != 7) = false by rw [cell]; rfl, Bool.false_eq_true, ite_false]
    exact FrameHeap.advance_valid valid actHandle actTag rest
  · have test : (kind s stack != 7) = true := bne_iff_ne.mpr cell
    simp only [test, ite_true]
    exact Heap.fail_valid valid 4

theorem storeSlot_valid {s : Array UInt64} {cap : Nat} {slot : UInt64}
    (valid : Heap.Valid s cap) (activation : kind s (read s 2) = 5)
    (slotCell : slot = 0 ∨ kind s slot = 7) : Heap.Valid (storeSlot s slot) cap := by
  by_cases zero : slot = 0
  · simp only [storeSlot, zero, BEq.rfl, ite_true]
    exact Heap.fail_valid valid 2
  · have slotTag : kind s slot = 7 := slotCell.resolve_left zero
    have slotHandle := kind_handle valid.1.1 (by decide) slotTag
    have slotField : field s slot 0 = 7 := (kind_eq_field valid.1.1 slotHandle).symm.trans slotTag
    have actHandle := kind_handle valid.1.1 (by decide) activation
    have actTag : field s (read s 2) 0 = 5 := (kind_eq_field valid.1.1 actHandle).symm.trans activation
    let stack := field s (read s 2) 7
    change Heap.Valid (if slot == 0 then fail s 2 else if kind s stack != 7 then fail s 4
      else advance (write s (address slot + 2) (field s stack 2)) (field s stack 3)) cap
    by_cases cell : kind s stack = 7
    · have handle := kind_handle valid.1.1 (by decide) cell
      have tag : field s stack 0 = 7 := (kind_eq_field valid.1.1 handle).symm.trans cell
      have value := pointer_value valid.1 handle (by rw [tag]; decide)
        (show (2 : UInt64).toNat < 8 by decide) (by rw [tag]; simp [PointerField])
      have rest := pointer_value valid.1 handle (by rw [tag]; decide)
        (show (3 : UInt64).toNat < 8 by decide) (by rw [tag]; simp [PointerField])
      have written := write_cell_valid valid slotHandle (by rw [slotField]; decide)
        (show (2 : UInt64).toNat < 8 by decide) (show (2 : UInt64) ≠ 0 by decide) (fun _ => value)
      have current := cell_register valid.1.1 slotHandle (show (2 : UInt64).toNat < 8 by decide)
        (show (2 : UInt64).toNat < 24 by decide) (v := field s stack 2)
      have postTag : field (write s (address slot + 2) (field s stack 2)) (read s 2) 0 = 5 := by
        rw [cell_tag valid.1.1 slotHandle (show (2 : UInt64).toNat < 8 by decide) (by decide) actHandle]
        exact actTag
      simp only [show (slot == 0) = false from beq_eq_false_iff_ne.mpr zero,
        Bool.false_eq_true, ite_false, show (kind s stack != 7) = false by rw [cell]; rfl]
      apply FrameHeap.advance_valid written
      · rw [current]; exact actHandle
      · rw [current]; exact postTag
      · exact FrameHeap.value_after_cell valid.1.1 slotHandle (show (2 : UInt64).toNat < 8 by decide) (by decide) rest
    · simp only [show (slot == 0) = false from beq_eq_false_iff_ne.mpr zero,
        Bool.false_eq_true, ite_false, show (kind s stack != 7) = true from bne_iff_ne.mpr cell, ite_true]
      exact Heap.fail_valid valid 4

end Project.Smalltalk.StackWrite
