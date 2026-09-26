import Lean

open Lean

namespace LeanExe.Extract.Core

/-! Total syntax operations shared by the production extractor and its proofs.
Metadata is discarded only along the traversed application or binder spine;
argument expressions and binder bodies are otherwise preserved.
-/

def appFnArgsAux (expr : Expr) (args : List Expr) : Expr × List Expr :=
  match expr with
  | .mdata _ body => appFnArgsAux body args
  | .app fn arg => appFnArgsAux fn (arg :: args)
  | other => (other, args)

def appFnArgs (expr : Expr) : Expr × List Expr :=
  appFnArgsAux expr []

def collectLambdas (expr : Expr) : Nat → Option Expr
  | 0 => some expr
  | count + 1 =>
      match expr.consumeMData with
      | .lam _ _ body _ => collectLambdas body count
      | _ => none
termination_by structural count => count

def peelForall (expr : Expr) : List Expr × Expr :=
  match expr with
  | .mdata _ body => peelForall body
  | .forallE _ domain body _ =>
      let rest := peelForall body
      (domain :: rest.fst, rest.snd)
  | other => ([], other)

def rebuildApp (fn : Expr) : List Expr → Expr
  | [] => fn
  | arg :: rest => rebuildApp (.app fn arg) rest

/-- Remove metadata along the function spine, leaving all arguments intact. -/
def stripAppMetadata : Expr → Expr
  | .mdata _ body => stripAppMetadata body
  | .app fn arg => .app (stripAppMetadata fn) arg
  | other => other

theorem rebuildApp_append (fn : Expr) (xs ys : List Expr) :
    rebuildApp fn (xs ++ ys) = rebuildApp (rebuildApp fn xs) ys := by
  induction xs generalizing fn with
  | nil => rfl
  | cons x xs ih => exact ih (.app fn x)

theorem appFnArgsAux_append (expr : Expr) (xs ys : List Expr) :
    appFnArgsAux expr (xs ++ ys) =
      ((appFnArgsAux expr xs).1, (appFnArgsAux expr xs).2 ++ ys) := by
  induction expr generalizing xs with
  | app fn arg ih _ => exact ih (arg :: xs)
  | mdata _ body ih => exact ih xs
  | _ => rfl

theorem rebuildApp_appFnArgsAux (expr : Expr) (args : List Expr) :
    rebuildApp (appFnArgsAux expr args).1 (appFnArgsAux expr args).2 =
      rebuildApp (stripAppMetadata expr) args := by
  induction expr generalizing args with
  | app fn arg ih _ => exact ih (arg :: args)
  | mdata _ body ih => exact ih args
  | _ => rfl

/-- Decomposition loses no executable application syntax. -/
theorem rebuildApp_appFnArgs (expr : Expr) :
    rebuildApp (appFnArgs expr).1 (appFnArgs expr).2 = stripAppMetadata expr :=
  rebuildApp_appFnArgsAux expr []

theorem appFnArgsAux_consumeMData (expr : Expr) (args : List Expr) :
    appFnArgsAux expr.consumeMData args = appFnArgsAux expr args := by
  induction expr with
  | mdata _ body ih => exact ih
  | _ => rfl

theorem peelForall_consumeMData (expr : Expr) :
    peelForall expr.consumeMData = peelForall expr := by
  induction expr with
  | mdata _ body ih => exact ih
  | _ => rfl

@[simp] theorem collectLambdas_zero (expr : Expr) : collectLambdas expr 0 = some expr := rfl

@[simp] theorem collectLambdas_lam (name : Name) (type body : Expr)
    (bi : BinderInfo) (n : Nat) :
    collectLambdas (.lam name type body bi) (n + 1) = collectLambdas body n := rfl

end LeanExe.Extract.Core
