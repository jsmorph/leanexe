import Verified.Tree

namespace Verified

def Tree.foldlWith {α : Type}
    (step : Tree listShape → UInt64 → Tree listShape → α → α) : Tree listShape → α → α
  | .nil, acc => acc
  | .node words children, acc =>
    foldlWith step (children ⟨0, by decide⟩)
      (step (.node words children) (words ⟨0, by decide⟩) (children ⟨0, by decide⟩) acc)

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
