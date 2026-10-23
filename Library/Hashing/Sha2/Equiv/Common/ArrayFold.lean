import Mathlib.Tactic.TypeStar

/-! # Common: `Array.foldl ∘ Array.ofFn` ↔ `Fin.foldl`

`Array.foldl` over `Array.ofFn g` collapses into `Fin.foldl`, and
`Fin.foldl` is extensional under equality of the fold step. -/

namespace SHS.Equiv.ArrayFold

/-- Folding over an `Array.ofFn` is the same as `Fin.foldl` over the
generating function. -/
theorem array_foldl_ofFn_eq_fin_foldl {α β : Type*} (n : Nat) (g : Fin n → α)
    (f : β → α → β) (init : β) :
    (Array.ofFn g).foldl f init = Fin.foldl n (fun b i => f b (g i)) init := by
  induction n generalizing init with
  | zero => simp
  | succ k ih =>
    rw [Array.ofFn_succ, Array.foldl_push, Fin.foldl_succ_last, ih]
    rfl

/-- `Fin.foldl` is extensional under pointwise equality of the step. -/
theorem fin_foldl_ext {α} (n : Nat) (f g : α → Fin n → α) (init : α)
    (h : ∀ s i, f s i = g s i) :
    Fin.foldl n f init = Fin.foldl n g init := by
  induction n generalizing init with
  | zero => simp
  | succ k ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, h, ih _ _ _ (fun _ _ => h _ _)]

end SHS.Equiv.ArrayFold
