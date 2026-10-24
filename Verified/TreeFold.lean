import Verified.Tree

namespace Verified

def Tree.foldlWith {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α) : Tree listShape → α → α
  | .nil _, acc => acc
  | .node r words children, acc =>
    foldlWith step (children ⟨0, listShape_children_pos r⟩)
      (step (.node r words children) (words ⟨0, listShape_words_pos r⟩)
        (children ⟨0, listShape_children_pos r⟩) acc)

def Tree.foldCostWith {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α)
    (charge : Tree listShape → UInt64 → Tree listShape → α → Nat) :
    Tree listShape → α → Nat
  | .nil _, _ => 0
  | .node r words children, acc =>
    charge (.node r words children) (words ⟨0, listShape_words_pos r⟩)
        (children ⟨0, listShape_children_pos r⟩) acc +
      foldCostWith step charge (children ⟨0, listShape_children_pos r⟩)
        (step (.node r words children) (words ⟨0, listShape_words_pos r⟩)
        (children ⟨0, listShape_children_pos r⟩) acc)

def Tree.foldFitsWith {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α)
    (valid : Tree listShape → UInt64 → Tree listShape → α → Bool) :
    Tree listShape → α → Bool
  | .nil _, _ => true
  | .node r words children, acc =>
    valid (.node r words children) (words ⟨0, listShape_words_pos r⟩)
        (children ⟨0, listShape_children_pos r⟩) acc &&
      foldFitsWith step valid (children ⟨0, listShape_children_pos r⟩)
        (step (.node r words children) (words ⟨0, listShape_words_pos r⟩)
        (children ⟨0, listShape_children_pos r⟩) acc)

theorem listCell_words_eq {α : Type} (words : Fin (listShape.words listCell) → α) :
    words = fun _ => words ⟨0, listShape_words_pos listCell⟩ := by
  funext i
  apply congrArg words
  apply Fin.ext
  have hi : i.val < listShape.words listCell := i.isLt
  have hOne : listShape.words listCell = 1 := by decide
  change i.val = 0
  omega

theorem listCell_children_eq {α : Type} (children : Fin (listShape.children listCell) → α) :
    children = fun _ => children ⟨0, listShape_children_pos listCell⟩ := by
  funext i
  apply congrArg children
  apply Fin.ext
  have hi : i.val < listShape.children listCell := i.isLt
  have hOne : listShape.children listCell = 1 := by decide
  change i.val = 0
  omega

@[simp] theorem Tree.foldCostWith_zero {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α)
    (root : Tree listShape) (init : α) :
    root.foldCostWith step (fun _ _ _ _ => 0) init = 0 := by
  induction root generalizing init with
  | nil => rfl
  | node r words children ih => simp only [foldCostWith, ih, Nat.zero_add]

@[simp] theorem Tree.foldFitsWith_true {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α)
    (root : Tree listShape) (init : α) :
    root.foldFitsWith step (fun _ _ _ _ => true) init = true := by
  induction root generalizing init with
  | nil => rfl
  | node r words children ih => simp only [foldFitsWith, ih, Bool.true_and]

theorem Tree.foldlWith_ofList {α β : Type} (flatten : α → β)
    (step : Tree listShape → UInt64 → Tree listShape → β → β)
    (native : α → UInt64 → α)
    (hstep : ∀ head tail acc,
      step (Tree.ofList (head :: tail)) head (Tree.ofList tail) (flatten acc) =
        flatten (native acc head)) (xs : List UInt64) (init : α) :
    Tree.foldlWith step (Tree.ofList xs) (flatten init) = flatten (xs.foldl native init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons head tail ih =>
    change Tree.foldlWith step (Tree.ofList tail)
      (step (Tree.ofList (head :: tail)) head (Tree.ofList tail) (flatten init)) = _
    rw [hstep]
    exact ih (native init head)

end Verified
