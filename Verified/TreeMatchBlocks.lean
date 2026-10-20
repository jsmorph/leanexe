import Verified.TreeLayout

namespace Verified

open Wasm LeanExe.Pipeline

theorem treeSlots_blocks_read (store : Store Unit) (p : UInt64) (fields : List Bool) :
    ∀ start words children,
      slotsBlocks store p start (treeSlots fields words children) =
        (List.ofFn fun i => (children i).blocks store
          (store.mem.read64 (slotAddress p
            (start + (fieldPosition true fields i).val)))).flatten := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    intro start words children
    cases bit
    · simp only [treeSlots, slotsBlocks, fieldPosition,
        dite_eq_right (by decide : false ≠ true), Fin.val_succ]
      rw [ih]
      simp only [Nat.add_assoc, Nat.add_comm 1]
      congr 1
    · simp only [treeSlots, slotsBlocks, ih, List.count_cons, beq_self_eq_true, ite_true,
        List.ofFn_succ, List.flatten_cons]
      simp only [fieldPosition, dite_eq_left rfl, Fin.val_succ, Fin.val_zero,
        Nat.zero_add, Nat.add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero,
        dite_eq_right, Nat.add_assoc, Nat.add_comm 1]
      congr 1

theorem treeSlots_regions_read (store : Store Unit) (p : UInt64) (fields : List Bool) :
    ∀ start words children,
      slotsRegions store p start (treeSlots fields words children) =
        (List.ofFn fun i => (children i).slotRegions store
          (store.mem.read64 (slotAddress p
            (start + (fieldPosition true fields i).val)))).flatten := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    intro start words children
    cases bit
    · simp only [treeSlots, slotsRegions, fieldPosition,
        dite_eq_right (by decide : false ≠ true), Fin.val_succ]
      rw [ih]
      simp only [Nat.add_assoc, Nat.add_comm 1]
      congr 1
    · simp only [treeSlots, slotsRegions, ih, List.count_cons, beq_self_eq_true, ite_true,
        List.ofFn_succ, List.flatten_cons]
      simp only [fieldPosition, dite_eq_left rfl, Fin.val_succ, Fin.val_zero,
        Nat.zero_add, Nat.add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero,
        dite_eq_right, Nat.add_assoc, Nat.add_comm 1]
      congr 1

end Verified
