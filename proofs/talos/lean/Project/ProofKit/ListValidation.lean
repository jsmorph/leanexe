import Mathlib.Data.List.Monad

namespace Project.ProofKit.ListValidation

def scan {α β : Type} (predicate : α → Bool) (error : β) (items : List α) : Id (Option β × Unit) :=
  forIn items (none, ()) fun item _ =>
    if !predicate item then pure (ForInStep.done (some error, ()))
    else pure (ForInStep.yield (none, ()))

theorem scan_eq {α β : Type} (predicate : α → Bool) (error : β) (items : List α) :
    scan predicate error items = if items.all predicate then (none, ()) else (some error, ()) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    simp only [scan] at ih ⊢
    cases h : predicate item <;> simp [List.forIn_cons, h] at ih ⊢
    · rfl
    · exact ih

#print axioms scan_eq
end Project.ProofKit.ListValidation
