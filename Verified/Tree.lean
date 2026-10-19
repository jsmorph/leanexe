import LeanExe.Pipeline.Slotted

namespace Verified

open LeanExe.Pipeline

structure TreeShape where
  fields : List Bool
  nonempty : fields ≠ []
  short : fields.length ≤ 64
  deriving DecidableEq, Repr

def TreeShape.words (shape : TreeShape) : Nat := shape.fields.count false

def TreeShape.children (shape : TreeShape) : Nat := shape.fields.count true

inductive Tree (shape : TreeShape) where
  | nil
  | node (words : Fin shape.words → UInt64) (children : Fin shape.children → Tree shape)

def treeSlots : (fields : List Bool) →
    (Fin (fields.count false) → UInt64) → (Fin (fields.count true) → Node) → List Slot
  | [], _, _ => []
  | false :: rest, words, children =>
    .word (words ⟨0, by simp⟩) ::
      treeSlots rest
        (fun i => words ⟨i.val + 1, by simp⟩)
        (fun i => children ⟨i.val, by simp⟩)
  | true :: rest, words, children =>
    .child (children ⟨0, by simp⟩) ::
      treeSlots rest
        (fun i => words ⟨i.val, by simp⟩)
        (fun i => children ⟨i.val + 1, by simp⟩)

theorem treeSlots_length (fields : List Bool) :
    ∀ words children, (treeSlots fields words children).length = fields.length := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih =>
    cases bit <;> intros <;> simp only [treeSlots, List.length_cons, ih]

theorem treeSlots_slotted (fields : List Bool) :
    ∀ words children, (∀ i, (children i).Slotted) →
      slotsSlotted (treeSlots fields words children) := by
  induction fields with
  | nil => intros; trivial
  | cons bit rest ih =>
    cases bit <;> intro words children hc <;> simp only [treeSlots, slotsSlotted]
    · exact ih _ _ (fun i => hc _)
    · exact ⟨hc _, ih _ _ (fun i => hc _)⟩

def Tree.toNode {shape : TreeShape} : Tree shape → Node
  | .nil => .null
  | .node words children =>
    .record (treeSlots shape.fields words (fun i => (children i).toNode))

theorem Tree.toNode_slotted {shape : TreeShape} (tree : Tree shape) : tree.toNode.Slotted := by
  induction tree with
  | nil => trivial
  | node words children ih =>
    refine ⟨?_, treeSlots_slotted _ _ _ ih⟩
    intro h
    have hl := congrArg List.length h
    exact shape.nonempty (List.eq_nil_of_length_eq_zero
      ((treeSlots_length shape.fields words (fun i => (children i).toNode)).symm.trans hl))

instance {shape : TreeShape} : Encode (Tree shape) := ⟨Tree.toNode⟩

instance {shape : TreeShape} : EncodeSlotted (Tree shape) := ⟨Tree.toNode_slotted⟩

def listShape : TreeShape := ⟨[false, true], by decide, by decide⟩

def Tree.ofList : List UInt64 → Tree listShape
  | [] => .nil
  | x :: xs => .node (fun _ => x) (fun _ => ofList xs)

def Tree.toList : Tree listShape → List UInt64
  | .nil => []
  | .node words children => words ⟨0, by decide⟩ :: toList (children ⟨0, by decide⟩)

@[simp] theorem Tree.toList_ofList (xs : List UInt64) : (ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

@[simp] theorem Tree.ofList_toList (tree : Tree listShape) : ofList tree.toList = tree := by
  induction tree with
  | nil => rfl
  | node words children ih =>
    simp only [ofList, toList, ih]
    congr 1 <;> funext i <;>
      have hi : i = ⟨0, by decide⟩ := by
        apply Fin.ext
        change i.val = 0
        have := i.isLt
        change i.val < 1 at this
        omega
    all_goals subst i; rfl

@[simp] theorem Tree.toNode_ofList (xs : List UInt64) : (ofList xs).toNode = encodeList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (fun n => Node.record [.word x, .child n]) ih

#print axioms Tree.toNode_slotted
#print axioms Tree.toList_ofList
#print axioms Tree.ofList_toList
#print axioms Tree.toNode_ofList

end Verified
