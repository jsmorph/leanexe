import Verified.TreeFieldBlocks
import Verified.TreeFieldValues

namespace Verified

open Wasm LeanExe.Pipeline

theorem treeFieldBlocks_eq (store : Store Unit) (fields : List Bool) :
    ∀ words pointers children,
      fieldBlocks store (treeFieldValues fields words pointers) (treeSlots fields words children) =
        (List.ofFn fun i => (children i).blocks store (pointers i)).flatten := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    intro words pointers children
    cases bit
    · simp only [treeFieldValues, treeSlots, fieldBlocks, Slot.valueBlocks, List.nil_append]
      exact ih _ _ _
    · simp only [treeFieldValues, treeSlots, fieldBlocks, Slot.valueBlocks]
      rw [ih]
      simp only [List.count_cons, beq_self_eq_true, ite_true, List.ofFn_succ,
        List.flatten_cons]
      congr 1

end Verified
