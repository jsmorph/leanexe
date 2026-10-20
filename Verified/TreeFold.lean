import Verified.Tree

namespace Verified

def Tree.foldlWith {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α) : Tree listShape → α → α
  | .nil, acc => acc
  | .node words children, acc =>
    foldlWith step (children ⟨0, by decide⟩)
      (step (.node words children) (words ⟨0, by decide⟩) (children ⟨0, by decide⟩) acc)

def Tree.foldCostWith {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α)
    (charge : Tree listShape → UInt64 → Tree listShape → α → Nat) :
    Tree listShape → α → Nat
  | .nil, _ => 0
  | .node words children, acc =>
    charge (.node words children) (words ⟨0, by decide⟩) (children ⟨0, by decide⟩) acc +
      foldCostWith step charge (children ⟨0, by decide⟩)
        (step (.node words children) (words ⟨0, by decide⟩) (children ⟨0, by decide⟩) acc)

def Tree.foldFitsWith {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α)
    (valid : Tree listShape → UInt64 → Tree listShape → α → Bool) :
    Tree listShape → α → Bool
  | .nil, _ => true
  | .node words children, acc =>
    valid (.node words children) (words ⟨0, by decide⟩) (children ⟨0, by decide⟩) acc &&
      foldFitsWith step valid (children ⟨0, by decide⟩)
        (step (.node words children) (words ⟨0, by decide⟩) (children ⟨0, by decide⟩) acc)

@[simp] theorem Tree.foldCostWith_zero {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α)
    (root : Tree listShape) (init : α) :
    root.foldCostWith step (fun _ _ _ _ => 0) init = 0 := by
  induction root generalizing init with
  | nil => rfl
  | node words children ih => simp only [foldCostWith, ih, Nat.zero_add]

@[simp] theorem Tree.foldFitsWith_true {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α)
    (root : Tree listShape) (init : α) :
    root.foldFitsWith step (fun _ _ _ _ => true) init = true := by
  induction root generalizing init with
  | nil => rfl
  | node words children ih => simp only [foldFitsWith, ih, Bool.true_and]

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
