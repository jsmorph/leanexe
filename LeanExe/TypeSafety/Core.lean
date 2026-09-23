import Std

/-!
# An independent first-order core

This module does not import the extractor, IR evaluator, or WebAssembly emitter.
Expressions and values are untyped syntax; their typing judgments are separate.
Variables use de Bruijn indices, with index zero denoting the newest binding.

The initial fragment contains `Unit`, `Bool`, bounded natural numbers, products,
binary sums, bindings, conditionals, and checked addition. `nat64` is a bounded
natural-number interpretation, not modular unsigned arithmetic.
-/

namespace LeanExe.TypeSafety

inductive Ty where
  | unit
  | bool
  | nat64
  | prod (left right : Ty)
  | sum (left right : Ty)
  deriving DecidableEq, Repr

/-- The exclusive upper bound on a represented natural number. -/
def nat64Limit : Nat := 2 ^ 64

inductive Expr where
  | var (index : Nat)
  | unit
  | bool (value : Bool)
  | nat (value : Nat)
  | letE (bound body : Expr)
  | ifE (condition yes no : Expr)
  | pair (left right : Expr)
  | fst (pair : Expr)
  | snd (pair : Expr)
  | inl (payload : Expr)
  | inr (payload : Expr)
  /-- Each branch binds its selected payload at index zero. -/
  | sumCase (scrutinee left right : Expr)
  | add (left right : Expr)
  deriving Repr

inductive Value where
  | unit
  | bool (value : Bool)
  | nat (value : Nat)
  | pair (left right : Value)
  | inl (payload : Value)
  | inr (payload : Value)
  deriving Repr

abbrev Context := List Ty
abbrev Env := List Value

/-- Total lookup; missing variables remain observably stuck in the machine. -/
def lookup {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => lookup xs n

inductive ExprTyped : Context → Expr → Ty → Prop where
  | var (found : lookup Γ index = some τ) : ExprTyped Γ (.var index) τ
  | unit : ExprTyped Γ .unit .unit
  | bool : ExprTyped Γ (.bool b) .bool
  | nat (bounded : n < nat64Limit) : ExprTyped Γ (.nat n) .nat64
  | letE : ExprTyped Γ bound α → ExprTyped (α :: Γ) body β →
      ExprTyped Γ (.letE bound body) β
  | ifE : ExprTyped Γ condition .bool → ExprTyped Γ yes τ →
      ExprTyped Γ no τ → ExprTyped Γ (.ifE condition yes no) τ
  | pair : ExprTyped Γ left α → ExprTyped Γ right β →
      ExprTyped Γ (.pair left right) (.prod α β)
  | fst : ExprTyped Γ pair (.prod α β) → ExprTyped Γ (.fst pair) α
  | snd : ExprTyped Γ pair (.prod α β) → ExprTyped Γ (.snd pair) β
  | inl : ExprTyped Γ payload α → ExprTyped Γ (.inl payload) (.sum α β)
  | inr : ExprTyped Γ payload β → ExprTyped Γ (.inr payload) (.sum α β)
  | sumCase : ExprTyped Γ scrutinee (.sum α β) →
      ExprTyped (α :: Γ) left τ → ExprTyped (β :: Γ) right τ →
      ExprTyped Γ (.sumCase scrutinee left right) τ
  | add : ExprTyped Γ left .nat64 → ExprTyped Γ right .nat64 →
      ExprTyped Γ (.add left right) .nat64

inductive ValueTyped : Value → Ty → Prop where
  | unit : ValueTyped .unit .unit
  | bool : ValueTyped (.bool b) .bool
  | nat (bounded : n < nat64Limit) : ValueTyped (.nat n) .nat64
  | pair : ValueTyped left α → ValueTyped right β →
      ValueTyped (.pair left right) (.prod α β)
  | inl : ValueTyped payload α → ValueTyped (.inl payload) (.sum α β)
  | inr : ValueTyped payload β → ValueTyped (.inr payload) (.sum α β)

inductive EnvTyped : Env → Context → Prop where
  | nil : EnvTyped [] []
  | cons : ValueTyped value τ → EnvTyped env Γ →
      EnvTyped (value :: env) (τ :: Γ)

/-- A typed variable always has a value of its declared type. -/
theorem EnvTyped.lookup (henv : EnvTyped env Γ)
    (found : lookup Γ index = some τ) :
    ∃ value, lookup env index = some value ∧ ValueTyped value τ := by
  induction henv generalizing index τ with
  | nil => simp [lookup] at found
  | @cons value α env Γ hvalue henv ih =>
      cases index with
      | zero =>
          simp only [lookup, Option.some.injEq] at found
          subst τ
          exact ⟨value, rfl, hvalue⟩
      | succ index =>
          exact ih found

theorem ValueTyped.bool_canonical (h : ValueTyped value .bool) :
    ∃ b, value = .bool b := by
  cases h with
  | bool => exact ⟨_, rfl⟩

theorem ValueTyped.nat_canonical (h : ValueTyped value .nat64) :
    ∃ n, value = .nat n ∧ n < nat64Limit := by
  cases h with
  | nat bounded => exact ⟨_, rfl, bounded⟩

theorem ValueTyped.prod_canonical (h : ValueTyped value (.prod α β)) :
    ∃ left right, value = .pair left right ∧
      ValueTyped left α ∧ ValueTyped right β := by
  cases h with
  | pair hleft hright => exact ⟨_, _, rfl, hleft, hright⟩

theorem ValueTyped.sum_canonical (h : ValueTyped value (.sum α β)) :
    (∃ payload, value = .inl payload ∧ ValueTyped payload α) ∨
    (∃ payload, value = .inr payload ∧ ValueTyped payload β) := by
  cases h with
  | inl hpayload => exact .inl ⟨_, rfl, hpayload⟩
  | inr hpayload => exact .inr ⟨_, rfl, hpayload⟩

end LeanExe.TypeSafety
