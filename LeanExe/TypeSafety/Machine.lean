import LeanExe.TypeSafety.Core

/-!
# Explicit call-by-value operational semantics

This is a left-to-right environment/continuation machine for the independent
core. Its evaluation order is a specification choice of this core, not a claim
about demand-based LeanExe extraction. Only the selected conditional or sum
branch executes. A let-bound expression evaluates before its body.

`step` returns `none` both for terminal states and for malformed/stuck states.
Consequently progress is substantive: a missing variable, a non-Boolean
condition, or a projection from a scalar is not silently relabeled a failure.
The only specified failure is checked natural-number addition overflow.
-/

namespace LeanExe.TypeSafety

inductive Frame where
  | letBody (body : Expr) (env : Env)
  | ifBranches (yes no : Expr) (env : Env)
  | pairLeft (right : Expr) (env : Env)
  | pairRight (left : Value)
  | fst
  | snd
  | inl
  | inr
  | sumBranches (left right : Expr) (env : Env)
  | addLeft (right : Expr) (env : Env)
  | addRight (left : Value)
  deriving Repr

abbrev Kont := List Frame

inductive State where
  | eval (expr : Expr) (env : Env) (kont : Kont)
  | ret (value : Value) (kont : Kont)
  | overflow (left right : Nat)
  deriving Repr

/-- Deterministic one-step execution, with malformed configurations stuck. -/
def step : State → Option State
  | .eval (.var index) env kont => (lookup env index).map (.ret · kont)
  | .eval .unit _ kont => some (.ret .unit kont)
  | .eval (.bool b) _ kont => some (.ret (.bool b) kont)
  | .eval (.nat n) _ kont => some (.ret (.nat n) kont)
  | .eval (.letE bound body) env kont =>
      some (.eval bound env (.letBody body env :: kont))
  | .eval (.ifE condition yes no) env kont =>
      some (.eval condition env (.ifBranches yes no env :: kont))
  | .eval (.pair left right) env kont =>
      some (.eval left env (.pairLeft right env :: kont))
  | .eval (.fst pair) env kont => some (.eval pair env (.fst :: kont))
  | .eval (.snd pair) env kont => some (.eval pair env (.snd :: kont))
  | .eval (.inl payload) env kont => some (.eval payload env (.inl :: kont))
  | .eval (.inr payload) env kont => some (.eval payload env (.inr :: kont))
  | .eval (.sumCase scrutinee left right) env kont =>
      some (.eval scrutinee env (.sumBranches left right env :: kont))
  | .eval (.add left right) env kont =>
      some (.eval left env (.addLeft right env :: kont))
  | .ret _ [] => none
  | .ret value (.letBody body env :: kont) =>
      some (.eval body (value :: env) kont)
  | .ret (.bool b) (.ifBranches yes no env :: kont) =>
      some (.eval (if b then yes else no) env kont)
  | .ret value (.pairLeft right env :: kont) =>
      some (.eval right env (.pairRight value :: kont))
  | .ret right (.pairRight left :: kont) => some (.ret (.pair left right) kont)
  | .ret (.pair left _) (.fst :: kont) => some (.ret left kont)
  | .ret (.pair _ right) (.snd :: kont) => some (.ret right kont)
  | .ret value (.inl :: kont) => some (.ret (.inl value) kont)
  | .ret value (.inr :: kont) => some (.ret (.inr value) kont)
  | .ret (.inl payload) (.sumBranches left _ env :: kont) =>
      some (.eval left (payload :: env) kont)
  | .ret (.inr payload) (.sumBranches _ right env :: kont) =>
      some (.eval right (payload :: env) kont)
  | .ret value (.addLeft right env :: kont) =>
      some (.eval right env (.addRight value :: kont))
  | .ret (.nat right) (.addRight (.nat left) :: kont) =>
      if left + right < nat64Limit then
        some (.ret (.nat (left + right)) kont)
      else some (.overflow left right)
  | .ret _ (_ :: _) => none
  | .overflow _ _ => none

def Step (before after : State) : Prop := step before = some after

/-- A return or an arithmetically justified overflow, never arbitrary stuckness. -/
def Terminal : State → Prop
  | .ret _ [] => True
  | .overflow left right =>
      left < nat64Limit ∧ right < nat64Limit ∧ nat64Limit ≤ left + right
  | _ => False

/-- The captured environment is part of each suspended expression's invariant. -/
inductive FrameTyped : Frame → Ty → Ty → Prop where
  | letBody : ExprTyped (α :: Γ) body β → EnvTyped env Γ →
      FrameTyped (.letBody body env) α β
  | ifBranches : ExprTyped Γ yes τ → ExprTyped Γ no τ → EnvTyped env Γ →
      FrameTyped (.ifBranches yes no env) .bool τ
  | pairLeft : ExprTyped Γ right β → EnvTyped env Γ →
      FrameTyped (.pairLeft right env) α (.prod α β)
  | pairRight : ValueTyped left α → FrameTyped (.pairRight left) β (.prod α β)
  | fst : FrameTyped .fst (.prod α β) α
  | snd : FrameTyped .snd (.prod α β) β
  | inl : FrameTyped .inl α (.sum α β)
  | inr : FrameTyped .inr β (.sum α β)
  | sumBranches : ExprTyped (α :: Γ) left τ → ExprTyped (β :: Γ) right τ →
      EnvTyped env Γ → FrameTyped (.sumBranches left right env) (.sum α β) τ
  | addLeft : ExprTyped Γ right .nat64 → EnvTyped env Γ →
      FrameTyped (.addLeft right env) .nat64 .nat64
  | addRight : ValueTyped left .nat64 → FrameTyped (.addRight left) .nat64 .nat64

/-- A continuation consumes the current type and eventually returns the result type. -/
inductive KontTyped : Kont → Ty → Ty → Prop where
  | nil : KontTyped [] τ τ
  | cons : FrameTyped frame α β → KontTyped rest β τ →
      KontTyped (frame :: rest) α τ

inductive StateTyped : State → Ty → Prop where
  | eval : ExprTyped Γ expr α → EnvTyped env Γ → KontTyped kont α τ →
      StateTyped (.eval expr env kont) τ
  | ret : ValueTyped value α → KontTyped kont α τ →
      StateTyped (.ret value kont) τ
  | overflow : left < nat64Limit → right < nat64Limit → nat64Limit ≤ left + right →
      StateTyped (.overflow left right) τ

/-- Reflexive, transitive execution; it does not assume termination. -/
inductive Steps : State → State → Prop where
  | refl : Steps state state
  | tail : Steps first middle → Step middle last → Steps first last

def initial (expr : Expr) : State := .eval expr [] []

theorem initial_typed (typed : ExprTyped [] expr τ) : StateTyped (initial expr) τ :=
  .eval typed .nil .nil

theorem step_deterministic (left : Step state next₁) (right : Step state next₂) :
    next₁ = next₂ := by
  exact Option.some.inj (left.symm.trans right)

end LeanExe.TypeSafety
