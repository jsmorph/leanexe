import Std

/-!
# An independent first-order core

This module does not import the extractor, IR evaluator, or WebAssembly emitter.
Expressions and values are untyped syntax; their typing judgments are separate.
Variables use de Bruijn indices, with index zero denoting the newest binding.
On entry to a function body, its fresh parameter environment places the first
argument at index zero, the second at index one, and so on. Local bindings then
prepend their values to that environment.

The fragment contains `Unit`, `Bool`, bounded natural numbers, products, binary
sums, bindings, conditionals, checked addition, and direct first-order calls.
`nat64` is a bounded natural-number interpretation, not modular unsigned
arithmetic. Function bodies may call any declared function, including themselves;
typing imposes no termination condition.
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
  | call (function : Nat) (arguments : List Expr)
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

structure Signature where
  params : List Ty
  result : Ty
  deriving Repr

abbrev Signatures := List Signature
/-- Body and signature indices identify functions; there are no function values. -/
abbrev Program := List Expr

/-- Total lookup; missing variables remain observably stuck in the machine. -/
def lookup {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => lookup xs n

mutual
inductive ExprTyped (signatures : Signatures) : Context → Expr → Ty → Prop where
  | var (found : lookup Γ index = some τ) : ExprTyped signatures Γ (.var index) τ
  | unit : ExprTyped signatures Γ .unit .unit
  | bool : ExprTyped signatures Γ (.bool b) .bool
  | nat (bounded : n < nat64Limit) : ExprTyped signatures Γ (.nat n) .nat64
  | letE : ExprTyped signatures Γ bound α → ExprTyped signatures (α :: Γ) body β →
      ExprTyped signatures Γ (.letE bound body) β
  | ifE : ExprTyped signatures Γ condition .bool → ExprTyped signatures Γ yes τ →
      ExprTyped signatures Γ no τ → ExprTyped signatures Γ (.ifE condition yes no) τ
  | pair : ExprTyped signatures Γ left α → ExprTyped signatures Γ right β →
      ExprTyped signatures Γ (.pair left right) (.prod α β)
  | fst : ExprTyped signatures Γ pair (.prod α β) → ExprTyped signatures Γ (.fst pair) α
  | snd : ExprTyped signatures Γ pair (.prod α β) → ExprTyped signatures Γ (.snd pair) β
  | inl : ExprTyped signatures Γ payload α → ExprTyped signatures Γ (.inl payload) (.sum α β)
  | inr : ExprTyped signatures Γ payload β → ExprTyped signatures Γ (.inr payload) (.sum α β)
  | sumCase : ExprTyped signatures Γ scrutinee (.sum α β) →
      ExprTyped signatures (α :: Γ) left τ → ExprTyped signatures (β :: Γ) right τ →
      ExprTyped signatures Γ (.sumCase scrutinee left right) τ
  | add : ExprTyped signatures Γ left .nat64 → ExprTyped signatures Γ right .nat64 →
      ExprTyped signatures Γ (.add left right) .nat64

  | call (found : lookup signatures function = some ⟨params, result⟩) :
      ArgsTyped signatures Γ arguments params →
      ExprTyped signatures Γ (.call function arguments) result

inductive ArgsTyped (signatures : Signatures) : Context → List Expr → List Ty → Prop where
  | nil : ArgsTyped signatures Γ [] []
  | cons : ExprTyped signatures Γ argument α → ArgsTyped signatures Γ rest types →
      ArgsTyped signatures Γ (argument :: rest) (α :: types)
end

/-- All function bodies use the same global signature table, allowing recursion. -/
inductive BodiesTyped (signatures : Signatures) : Program → Signatures → Prop where
  | nil : BodiesTyped signatures [] []
  | cons : ExprTyped signatures signature.params body signature.result →
      BodiesTyped signatures bodies rest →
      BodiesTyped signatures (body :: bodies) (signature :: rest)

/-- Every program body has exactly one matching declared signature. -/
abbrev ProgramTyped (program : Program) (signatures : Signatures) : Prop :=
  BodiesTyped signatures program signatures

/-- A declared callee exists and its body is typed in its parameter context. -/
theorem BodiesTyped.lookup (typed : BodiesTyped signatures program declarations)
    (found : lookup declarations function = some signature) :
    ∃ body, lookup program function = some body ∧
      ExprTyped signatures signature.params body signature.result := by
  induction typed generalizing function signature with
  | nil => simp [LeanExe.TypeSafety.lookup] at found
  | cons hbody hrest ih =>
      cases function with
      | zero =>
          simp only [LeanExe.TypeSafety.lookup, Option.some.injEq] at found
          subst signature
          exact ⟨_, rfl, hbody⟩
      | succ function => exact ih found

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

/-- Argument accumulation preserves the correspondence between values and types. -/
theorem EnvTyped.append (left : EnvTyped env Γ) (right : EnvTyped env' Δ) :
    EnvTyped (env ++ env') (Γ ++ Δ) := by
  induction left with
  | nil => exact right
  | cons hvalue henv ih => exact .cons hvalue ih

/-- A typed variable always has a value of its declared type. -/
theorem EnvTyped.lookup (henv : EnvTyped env Γ)
    (found : lookup Γ index = some τ) :
    ∃ value, lookup env index = some value ∧ ValueTyped value τ := by
  induction henv generalizing index τ with
  | nil => simp [LeanExe.TypeSafety.lookup] at found
  | @cons value α env Γ hvalue henv ih =>
      cases index with
      | zero =>
          simp only [LeanExe.TypeSafety.lookup, Option.some.injEq] at found
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
