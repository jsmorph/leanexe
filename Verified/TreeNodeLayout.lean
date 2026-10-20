import Verified.TreeLayout
import Verified.TreeCopyWork

namespace Verified

open LeanExe.Pipeline

mutual
def NodeLayout (shape : TreeShape) : Node → Prop
  | .null => True
  | .record slots => slots.length = shape.fields.length ∧ maskOf slots = shape.mask ∧
      SlotsLayout shape slots

def SlotsLayout (shape : TreeShape) : List Slot → Prop
  | [] => True
  | .word _ :: rest => SlotsLayout shape rest
  | .child value :: rest => NodeLayout shape value ∧ SlotsLayout shape rest
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

theorem Tree.toNode_layout {shape : TreeShape} (value : Tree shape) :
    NodeLayout shape value.toNode := by
  induction value with
  | nil => trivial
  | node words children ih =>
    exact ⟨treeSlots_length .., shape.mask_eq .., treeSlots_layout shape _ _ _ ih⟩

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

theorem Tree.toNode_records {shape : TreeShape} (value : Tree shape) :
    value.toNode.records = value.nodes := by
  induction value with
  | nil => rfl
  | node words children ih =>
    change 1 + slotsRecords (treeSlots shape.fields words (fun i => (children i).toNode)) =
      1 + (List.ofFn fun i => (children i).nodes).sum
    rw [treeSlots_records shape.fields words (fun i => (children i).toNode)]
    exact congrArg (fun f : Fin shape.children → Nat => 1 + (List.ofFn f).sum) (funext ih)

#print axioms Tree.toNode_layout
#print axioms Tree.toNode_records

end Verified
