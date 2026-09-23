import LeanExe.TypeSafety.Core

/-!
# Explicit call-by-value operational semantics

This is a left-to-right environment/continuation machine for the independent
core. Its evaluation order is a specification choice of this core, not a claim
about demand-based LeanExe extraction. Only the selected conditional or sum
branch executes. A let-bound expression evaluates before its body.
Call arguments evaluate left to right in the caller environment. The callee
receives a fresh environment containing exactly those argument values in order:
the first argument has index zero. Continuations retain any caller bindings
needed after the result returns. Recursive calls are allowed.

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
  | splitBody (body : Expr) (env : Env)
  | unitBody (body : Expr) (env : Env)
  | inl
  | inr
  | sumBranches (left right : Expr) (env : Env)
  | addLeft (right : Expr) (env : Env)
  | addRight (left : Value)
  /-- Arguments already computed, remaining argument expressions, and caller environment. -/
  | callArgs (function : Nat) (done : Env) (remaining : List Expr) (env : Env)
  deriving Repr

abbrev Kont := List Frame

inductive State where
  | eval (expr : Expr) (env : Env) (kont : Kont)
  | ret (value : Value) (kont : Kont)
  | overflow (left right : Nat)
  deriving Repr

/-- A missing function remains stuck rather than becoming a permitted failure. -/
def enterCall (program : Program) (function : Nat) (arguments : Env) (kont : Kont) :
    Option State :=
  (lookup program function).map (fun body => .eval body arguments kont)

/-- Deterministic one-step execution, with malformed configurations stuck. -/
def step (program : Program) : State → Option State
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
  | .eval (.split pair body) env kont =>
      some (.eval pair env (.splitBody body env :: kont))
  | .eval (.unitCase scrutinee body) env kont =>
      some (.eval scrutinee env (.unitBody body env :: kont))
  | .eval (.inl payload) env kont => some (.eval payload env (.inl :: kont))
  | .eval (.inr payload) env kont => some (.eval payload env (.inr :: kont))
  | .eval (.sumCase scrutinee left right) env kont =>
      some (.eval scrutinee env (.sumBranches left right env :: kont))
  | .eval (.add left right) env kont =>
      some (.eval left env (.addLeft right env :: kont))
  | .eval (.call function []) _ kont => enterCall program function [] kont
  | .eval (.call function (argument :: rest)) env kont =>
      some (.eval argument env (.callArgs function [] rest env :: kont))
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
  | .ret (.pair left right) (.splitBody body env :: kont) =>
      some (.eval body (left :: right :: env) kont)
  | .ret .unit (.unitBody body env :: kont) => some (.eval body env kont)
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
  | .ret value (.callArgs function done [] _ :: kont) =>
      enterCall program function (done ++ [value]) kont
  | .ret value (.callArgs function done (argument :: rest) env :: kont) =>
      some (.eval argument env (.callArgs function (done ++ [value]) rest env :: kont))
  | .ret _ (_ :: _) => none
  | .overflow _ _ => none

def Step (program : Program) (before after : State) : Prop := step program before = some after

/-- A return or an arithmetically justified overflow, never arbitrary stuckness. -/
def Terminal : State → Prop
  | .ret _ [] => True
  | .overflow left right =>
      left < nat64Limit ∧ right < nat64Limit ∧ nat64Limit ≤ left + right
  | _ => False

/-- The captured environment is part of each suspended expression's invariant. -/
inductive FrameTyped (signatures : Signatures) : Frame → Ty → Ty → Prop where
  | letBody : ExprTyped signatures (α :: Γ) body β → EnvTyped env Γ →
      FrameTyped signatures (.letBody body env) α β
  | ifBranches : ExprTyped signatures Γ yes τ → ExprTyped signatures Γ no τ → EnvTyped env Γ →
      FrameTyped signatures (.ifBranches yes no env) .bool τ
  | pairLeft : ExprTyped signatures Γ right β → EnvTyped env Γ →
      FrameTyped signatures (.pairLeft right env) α (.prod α β)
  | pairRight : ValueTyped left α → FrameTyped signatures (.pairRight left) β (.prod α β)
  | fst : FrameTyped signatures .fst (.prod α β) α
  | snd : FrameTyped signatures .snd (.prod α β) β
  | splitBody : ExprTyped signatures (α :: β :: Γ) body τ → EnvTyped env Γ →
      FrameTyped signatures (.splitBody body env) (.prod α β) τ
  | unitBody : ExprTyped signatures Γ body τ → EnvTyped env Γ →
      FrameTyped signatures (.unitBody body env) .unit τ
  | inl : FrameTyped signatures .inl α (.sum α β)
  | inr : FrameTyped signatures .inr β (.sum α β)
  | sumBranches : ExprTyped signatures (α :: Γ) left τ → ExprTyped signatures (β :: Γ) right τ →
      EnvTyped env Γ → FrameTyped signatures (.sumBranches left right env) (.sum α β) τ
  | addLeft : ExprTyped signatures Γ right .nat64 → EnvTyped env Γ →
      FrameTyped signatures (.addLeft right env) .nat64 .nat64
  | addRight : ValueTyped left .nat64 → FrameTyped signatures (.addRight left) .nat64 .nat64

  | callArgs (found : lookup signatures function = some ⟨params, result⟩) :
      EnvTyped done doneTypes → ArgsTyped signatures Γ remaining remainingTypes →
      EnvTyped env Γ → doneTypes ++ (α :: remainingTypes) = params →
      FrameTyped signatures (.callArgs function done remaining env) α result

/-- A continuation consumes the current type and eventually returns the result type. -/
inductive KontTyped (signatures : Signatures) : Kont → Ty → Ty → Prop where
  | nil : KontTyped signatures [] τ τ
  | cons : FrameTyped signatures frame α β → KontTyped signatures rest β τ →
      KontTyped signatures (frame :: rest) α τ

inductive StateTyped (signatures : Signatures) : State → Ty → Prop where
  | eval : ExprTyped signatures Γ expr α → EnvTyped env Γ → KontTyped signatures kont α τ →
      StateTyped signatures (.eval expr env kont) τ
  | ret : ValueTyped value α → KontTyped signatures kont α τ →
      StateTyped signatures (.ret value kont) τ
  | overflow : left < nat64Limit → right < nat64Limit → nat64Limit ≤ left + right →
      StateTyped signatures (.overflow left right) τ

/-- Reflexive, transitive execution; it does not assume termination. -/
inductive Steps (program : Program) : State → State → Prop where
  | refl : Steps program state state
  | tail : Steps program first middle → Step program middle last → Steps program first last

def initial (expr : Expr) : State := .eval expr [] []

theorem initial_typed (typed : ExprTyped signatures [] expr τ) :
    StateTyped signatures (initial expr) τ :=
  .eval typed .nil .nil

theorem step_deterministic (left : Step program state next₁) (right : Step program state next₂) :
    next₁ = next₂ := by
  exact Option.some.inj (left.symm.trans right)

end LeanExe.TypeSafety
