import Verified.TreeAssembleTyped
import Verified.TreeDetach

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem slotsBlocks_get_sublist (store : Store Unit) (p : UInt64) :
    ∀ (slots : List LeanExe.Pipeline.Slot) i j (hj : j < slots.length),
      List.Sublist (slotsBlocks store p (i + j) [slots[j]]) (slotsBlocks store p i slots)
  | [], _, _, hj => by simp at hj
  | slot :: slots, i, 0, _ => by
    cases slot
    · simp only [List.getElem_cons_zero, slotsBlocks]
      exact List.nil_sublist _
    · simpa only [List.getElem_cons_zero, slotsBlocks, List.append_nil, Nat.add_zero] using
        List.sublist_append_left _ (slotsBlocks store p (i + 1) slots)
  | slot :: slots, i, j + 1, hj => by
    have h := slotsBlocks_get_sublist store p slots (i + 1) j (by simpa using hj)
    cases slot
    · simpa only [slotsBlocks, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using h
    · simp only [List.getElem_cons_succ, slotsBlocks]
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact h.trans (List.sublist_append_right _ _)

theorem Mode.node.borrow {mode : Mode} {heap : Heap} {store : Store Unit}
    {p : UInt64} {value : Node} (h : mode.node heap store p value) :
    NodeBorrowed heap store p value := by
  cases mode
  · exact h
  · exact NodeOwned.borrowed p value h.1

theorem treeSlots_child_owned {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {p : UInt64} {words : Fin shape.words → UInt64} {children : Fin shape.children → Tree shape}
    (hSlots : SlotsOwned heap store p 0
      (treeSlots shape.fields words (fun i => (children i).toNode)))
    (hApart : (slotsBlocks store p 0
      (treeSlots shape.fields words (fun i => (children i).toNode))).Pairwise regionsDisjoint)
    (i : Fin shape.children) :
    Mode.owned.node heap store
      (store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val))
      (children i).toNode := by
  unfold TreeShape.words TreeShape.children at *
  have hi := SlotsOwned.get _ 0 hSlots (fieldPosition true shape.fields i).val
    (by rw [treeSlots_length]; exact (fieldPosition true shape.fields i).isLt)
  rw [Nat.zero_add, treeSlots_child_get] at hi
  refine ⟨hi.1, ?_⟩
  have hs := slotsBlocks_get_sublist store p
    (treeSlots shape.fields words (fun i => (children i).toNode)) 0
    (fieldPosition true shape.fields i).val
    (by rw [treeSlots_length]; exact (fieldPosition true shape.fields i).isLt)
  rw [Nat.zero_add, treeSlots_child_get] at hs
  simp only [slotsBlocks, List.append_nil] at hs
  exact hApart.sublist hs

theorem treeNode_word_read {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {p : UInt64} {words : Fin shape.words → UInt64}
    {children : Fin shape.children → Tree shape}
    (h : mode.node heap store p (Tree.node words children).toNode) (i : Fin shape.words) :
    store.mem.read64 (slotAddress p (fieldPosition false shape.fields i).val) = words i := by
  unfold TreeShape.words TreeShape.children at *
  have hSlots := h.borrow.2
  have hi := SlotsBorrowed.get _ 0 hSlots (fieldPosition false shape.fields i).val
    (by rw [treeSlots_length]; exact (fieldPosition false shape.fields i).isLt)
  rw [Nat.zero_add, treeSlots_word_get] at hi
  exact hi.1

theorem treeNode_child_rep {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {p : UInt64} {words : Fin shape.words → UInt64}
    {children : Fin shape.children → Tree shape}
    (h : mode.node heap store p (Tree.node words children).toNode)
    (i : Fin shape.children) :
    mode.node heap store
      (store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val))
      (children i).toNode := by
  unfold TreeShape.words TreeShape.children at *
  cases mode
  · have hi := SlotsBorrowed.get _ 0 h.2 (fieldPosition true shape.fields i).val
      (by rw [treeSlots_length]; exact (fieldPosition true shape.fields i).isLt)
    rw [Nat.zero_add, treeSlots_child_get] at hi
    exact hi.1
  · exact treeSlots_child_owned h.1.2 (List.pairwise_cons.mp h.2).2 i

end Verified
