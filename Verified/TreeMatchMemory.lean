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

theorem TreeShape.fieldStart_tagSlots (shape : TreeShape) (r : Fin shape.records) :
    shape.fieldStart = (shape.tagSlots r).length :=
  (shape.fieldStart_eq r).trans (shape.tagWords_length r)

theorem TreeShape.fieldSlot_lt (shape : TreeShape) (r : Fin shape.records) (bit : Bool)
    (i : Fin ((shape.fields r).count bit)) :
    shape.fieldStart + (fieldPosition bit (shape.fields r) i).val < shape.width r := by
  have := (fieldPosition bit (shape.fields r) i).isLt
  rw [shape.fieldStart_tagSlots r, TreeShape.width]
  omega

theorem tagSlots_blocks (store : Store Unit) (p : UInt64) (shape : TreeShape)
    (r : Fin shape.records) (i : Nat) : slotsBlocks store p i (shape.tagSlots r) = [] := by
  unfold TreeShape.tagSlots
  split <;> rfl

theorem recordSlots_blocks (store : Store Unit) (p : UInt64) (shape : TreeShape)
    (r : Fin shape.records) (words children) :
    slotsBlocks store p 0 (shape.recordSlots r words children) =
      slotsBlocks store p shape.fieldStart (treeSlots (shape.fields r) words children) := by
  unfold TreeShape.recordSlots
  rw [slotsBlocks_append, tagSlots_blocks, List.nil_append, Nat.zero_add,
    ← shape.fieldStart_tagSlots r]

theorem recordSlots_regions (store : Store Unit) (p : UInt64) (shape : TreeShape)
    (r : Fin shape.records) (words children) :
    slotsRegions store p 0 (shape.recordSlots r words children) =
      slotsRegions store p shape.fieldStart (treeSlots (shape.fields r) words children) := by
  unfold TreeShape.recordSlots
  rw [shape.fieldStart_tagSlots r]
  unfold TreeShape.tagSlots
  by_cases ht : shape.tagged = true <;> simp [ht, slotsRegions]

theorem treeSlots_child_owned {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {r : Fin shape.records} {p : UInt64} {start : Nat} {words : Fin (shape.words r) → UInt64}
    {children : Fin (shape.children r) → Tree shape}
    (hSlots : SlotsOwned heap store p start
      (treeSlots (shape.fields r) words (fun i => (children i).toNode)))
    (hApart : (slotsBlocks store p start
      (treeSlots (shape.fields r) words (fun i => (children i).toNode))).Pairwise
        regionsDisjoint)
    (i : Fin (shape.children r)) :
    Mode.owned.node heap store
      (store.mem.read64 (slotAddress p (start + (fieldPosition true (shape.fields r) i).val)))
      (children i).toNode := by
  unfold TreeShape.words TreeShape.children at *
  have hi := SlotsOwned.get _ start hSlots (fieldPosition true (shape.fields r) i).val
    (by rw [treeSlots_length]; exact (fieldPosition true (shape.fields r) i).isLt)
  rw [treeSlots_child_get] at hi
  refine ⟨hi.1, ?_⟩
  have hs := slotsBlocks_get_sublist store p
    (treeSlots (shape.fields r) words (fun i => (children i).toNode)) start
    (fieldPosition true (shape.fields r) i).val
    (by rw [treeSlots_length]; exact (fieldPosition true (shape.fields r) i).isLt)
  rw [treeSlots_child_get] at hs
  simp only [slotsBlocks, List.append_nil] at hs
  exact hApart.sublist hs

theorem treeNode_word_read {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {r : Fin shape.records} {p : UInt64}
    {words : Fin (shape.words r) → UInt64} {children : Fin (shape.children r) → Tree shape}
    (h : mode.node heap store p (Tree.node r words children).toNode) (i : Fin (shape.words r)) :
    store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition false (shape.fields r) i).val)) =
      words i := by
  have hSlots : SlotsBorrowed heap store p 0 (shape.tagSlots r ++
      treeSlots (shape.fields r) words (fun i => (children i).toNode)) := h.borrow.2
  obtain ⟨-, hFields⟩ := (SlotsBorrowed.append_iff _ _ _).mp hSlots
  rw [Nat.zero_add, ← shape.fieldStart_tagSlots r] at hFields
  unfold TreeShape.words TreeShape.children at *
  have hi := SlotsBorrowed.get _ _ hFields (fieldPosition false (shape.fields r) i).val
    (by rw [treeSlots_length]; exact (fieldPosition false (shape.fields r) i).isLt)
  rw [treeSlots_word_get] at hi
  exact hi.1

theorem treeNode_child_rep {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {r : Fin shape.records} {p : UInt64}
    {words : Fin (shape.words r) → UInt64} {children : Fin (shape.children r) → Tree shape}
    (h : mode.node heap store p (Tree.node r words children).toNode)
    (i : Fin (shape.children r)) :
    mode.node heap store
      (store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))
      (children i).toNode := by
  cases mode
  · have hSlots : SlotsBorrowed heap store p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) words (fun i => (children i).toNode)) := h.2
    obtain ⟨-, hFields⟩ := (SlotsBorrowed.append_iff _ _ _).mp hSlots
    rw [Nat.zero_add, ← shape.fieldStart_tagSlots r] at hFields
    unfold TreeShape.words TreeShape.children at *
    have hi := SlotsBorrowed.get _ _ hFields (fieldPosition true (shape.fields r) i).val
      (by rw [treeSlots_length]; exact (fieldPosition true (shape.fields r) i).isLt)
    rw [treeSlots_child_get] at hi
    exact hi.1
  · have hSlots : SlotsOwned heap store p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) words (fun i => (children i).toNode)) := h.1.2
    obtain ⟨-, hFields⟩ := (SlotsOwned.append_iff _ _ _).mp hSlots
    rw [Nat.zero_add, ← shape.fieldStart_tagSlots r] at hFields
    have hApart := (List.pairwise_cons.mp h.2).2
    change (slotsBlocks store p 0 (shape.tagSlots r ++
      treeSlots (shape.fields r) words (fun i => (children i).toNode))).Pairwise
        regionsDisjoint at hApart
    rw [slotsBlocks_append, tagSlots_blocks, List.nil_append, Nat.zero_add,
      ← shape.fieldStart_tagSlots r] at hApart
    exact treeSlots_child_owned hFields hApart i

end Verified
