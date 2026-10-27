import Verified.TreeLayout
import Verified.TreeCopyWork

namespace Verified

open LeanExe.Pipeline

mutual
theorem Node.blocks_length (store : Wasm.Store Unit) (ptr : UInt64) :
    (value : Node) → (value.blocks store ptr).length = value.records
  | .null => rfl
  | .record slots => by
    simp only [Node.blocks, List.length_cons, Node.records, slotsBlocks_length]
    omega

theorem slotsBlocks_length (store : Wasm.Store Unit) (ptr : UInt64) (i : Nat) :
    (slots : List Slot) → (slotsBlocks store ptr i slots).length = slotsRecords slots
  | [] => rfl
  | .word _ :: rest => slotsBlocks_length store ptr (i + 1) rest
  | .child value :: rest => by
    simp only [slotsBlocks, List.length_append, Node.blocks_length, slotsBlocks_length, slotsRecords]
  | .array _ :: rest => by
    simp only [slotsBlocks, List.length_cons, slotsBlocks_length, slotsRecords]
    omega
  | .bytes data :: rest => by
    simp only [slotsBlocks, List.length_append, List.length_map, slotsBlocks_length, slotsRecords]
    unfold bufferRoots
    split <;> rfl
end

mutual
def NodeLayout (shape : TreeShape) : Node → Prop
  | .null => True
  | .record slots => ∃ r, slots.length = shape.width r ∧ maskOf slots = shape.mask r ∧
      slots.take (shape.tagSlots r).length = shape.tagSlots r ∧ SlotsLayout shape slots

def SlotsLayout (shape : TreeShape) : List Slot → Prop
  | [] => True
  | .word _ :: rest => SlotsLayout shape rest
  | .child value :: rest => NodeLayout shape value ∧ SlotsLayout shape rest
  | .array _ :: _ => False
  | .bytes _ :: _ => False
end

mutual
theorem NodeLayout.slotted {shape : TreeShape} :
    ∀ {value : Node}, NodeLayout shape value → value.Slotted
  | .null, _ => trivial
  | .record slots, h => by
    obtain ⟨r, hLength, -, -, hSlots⟩ := h
    refine ⟨?_, SlotsLayout.slotted (slots := slots) hSlots⟩
    intro hEmpty
    rw [hEmpty] at hLength
    exact absurd hLength.symm (Nat.ne_of_gt (shape.width_pos r))

theorem SlotsLayout.slotted {shape : TreeShape} :
    ∀ {slots : List Slot}, SlotsLayout shape slots → slotsSlotted slots
  | [], _ => trivial
  | .word _ :: rest, h => SlotsLayout.slotted (slots := rest) h
  | .child value :: rest, h =>
    ⟨NodeLayout.slotted (value := value) h.1, SlotsLayout.slotted (slots := rest) h.2⟩
  | .array _ :: _, h => False.elim h
  | .bytes _ :: _, h => False.elim h
end

theorem treeSlots_layout (shape : TreeShape) (fields : List Bool) :
    ∀ words children, (∀ i, NodeLayout shape (children i)) →
      SlotsLayout shape (treeSlots fields words children) := by
  induction fields with
  | nil => intros; trivial
  | cons bit rest ih =>
    cases bit <;> intro words children hc <;> simp only [treeSlots, SlotsLayout]
    · exact ih _ _ (fun i => hc _)
    · exact ⟨hc _, ih _ _ (fun i => hc _)⟩

theorem tagSlots_layout (shape : TreeShape) (r : Fin shape.records) (rest : List Slot)
    (h : SlotsLayout shape rest) : SlotsLayout shape (shape.tagSlots r ++ rest) := by
  unfold TreeShape.tagSlots
  split
  · exact h
  · exact h

theorem Tree.toNode_layout {shape : TreeShape} (value : Tree shape) :
    NodeLayout shape value.toNode := by
  induction value with
  | nil => trivial
  | node r words children ih =>
    exact ⟨r, shape.recordSlots_length .., shape.mask_eq .., by simp [TreeShape.recordSlots],
      tagSlots_layout shape r _ (treeSlots_layout shape _ _ _ ih)⟩

theorem SlotsLayout.child {shape : TreeShape} :
    ∀ {slots : List Slot}, SlotsLayout shape slots →
      ∀ i (hi : i < slots.length) value, slots[i] = .child value → NodeLayout shape value
  | [], _, i, hi, _, _ => by simp at hi
  | .word _ :: rest, h, 0, _, _, he => by cases he
  | .word _ :: rest, h, i + 1, hi, value, he =>
    SlotsLayout.child (slots := rest) h i (by simpa using hi) value he
  | .child _ :: _, h, 0, _, _, he => by cases he; exact h.1
  | .child _ :: rest, h, i + 1, hi, value, he =>
    SlotsLayout.child (slots := rest) h.2 i (by simpa using hi) value he
  | .array _ :: _, h, _, _, _, _ => False.elim h
  | .bytes _ :: _, h, _, _, _, _ => False.elim h

/-- A slot of a record laid out by a shape is a word or a child. -/
theorem SlotsLayout.word_or_child {shape : TreeShape} :
    ∀ {slots : List Slot}, SlotsLayout shape slots → ∀ i (hi : i < slots.length),
      (∃ w, slots[i] = .word w) ∨ ∃ value, slots[i] = .child value
  | [], _, i, hi => by simp at hi
  | .word w :: _, _, 0, _ => .inl ⟨w, rfl⟩
  | .word _ :: rest, h, i + 1, hi =>
    SlotsLayout.word_or_child (slots := rest) h i (by simpa using hi)
  | .child value :: _, _, 0, _ => .inr ⟨value, rfl⟩
  | .child _ :: rest, h, i + 1, hi =>
    SlotsLayout.word_or_child (slots := rest) h.2 i (by simpa using hi)
  | .array _ :: _, h, _, _ => False.elim h
  | .bytes _ :: _, h, _, _ => False.elim h

theorem treeSlots_records (fields : List Bool) :
    ∀ words children, slotsRecords (treeSlots fields words children) =
      (List.ofFn fun i => (children i).records).sum := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    intro words children
    cases bit
    · simp only [treeSlots, slotsRecords]
      rw [ih]
      rfl
    · simp only [treeSlots, slotsRecords]
      rw [ih]
      simp only [List.count_cons, beq_self_eq_true, ite_true, List.ofFn_succ, List.sum_cons]
      rfl

theorem tagSlots_records (shape : TreeShape) (r : Fin shape.records) (words children) :
    slotsRecords (shape.recordSlots r words children) =
      slotsRecords (treeSlots (shape.fields r) words children) := by
  unfold TreeShape.recordSlots TreeShape.tagSlots
  split
  · rfl
  · rfl

theorem Tree.toNode_records {shape : TreeShape} (value : Tree shape) :
    value.toNode.records = value.nodes := by
  induction value with
  | nil => rfl
  | node r words children ih =>
    change 1 + slotsRecords (shape.recordSlots r (shape.slotWords r words)
        (fun i => (children i).toNode)) = 1 + (List.ofFn fun i => (children i).nodes).sum
    rw [tagSlots_records shape r]
    exact congrArg (1 + ·) ((treeSlots_records (shape.fields r) (shape.slotWords r words)
      (fun i => (children i).toNode)).trans
        (congrArg (fun f : Fin (shape.children r) → Nat => (List.ofFn f).sum) (funext ih)))

theorem treeSlots_copyCost (fields : List Bool) :
    ∀ words children, slotsCopyCost (treeSlots fields words children) =
      (List.ofFn fun i => nodeCopyCost (children i)).sum := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    intro words children
    cases bit
    · simp only [treeSlots, slotsCopyCost]
      rw [ih]
      rfl
    · simp only [treeSlots, slotsCopyCost]
      rw [ih]
      simp only [List.count_cons, beq_self_eq_true, ite_true, List.ofFn_succ, List.sum_cons]
      rfl

theorem tagSlots_copyCost (shape : TreeShape) (r : Fin shape.records) (words children) :
    slotsCopyCost (shape.recordSlots r words children) =
      slotsCopyCost (treeSlots (shape.fields r) words children) := by
  unfold TreeShape.recordSlots TreeShape.tagSlots
  split
  · rfl
  · rfl

theorem Tree.copyCost_eq {shape : TreeShape} (value : Tree shape) :
    value.copyCost = nodeCopyCost value.toNode := by
  induction value with
  | nil => rfl
  | node r words children ih =>
    change allocCost (8 * shape.width r) + (List.ofFn fun i => (children i).copyCost).sum =
      allocCost (8 * (shape.recordSlots r (shape.slotWords r words)
          (fun i => (children i).toNode)).length) +
        slotsCopyCost (shape.recordSlots r (shape.slotWords r words)
          (fun i => (children i).toNode))
    rw [shape.recordSlots_length, tagSlots_copyCost shape r]
    exact congrArg (allocCost (8 * shape.width r) + ·)
      ((congrArg (fun f : Fin (shape.children r) → Nat => (List.ofFn f).sum) (funext ih)).trans
        (treeSlots_copyCost (shape.fields r) (shape.slotWords r words)
          (fun i => (children i).toNode)).symm)

#print axioms Tree.toNode_layout
#print axioms Tree.toNode_records
#print axioms Tree.copyCost_eq
#print axioms NodeLayout.slotted
#print axioms SlotsLayout.word_or_child

end Verified
