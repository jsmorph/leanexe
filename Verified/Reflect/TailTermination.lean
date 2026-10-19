import Verified.Reflect.TailBody
import Verified.TailTransport

namespace Verified.Reflect

open Lean Meta Elab Term

def tailRelation (step stateType resultType : Lean.Expr) : MetaM Lean.Expr := do
  withLocalDeclD `next stateType fun next => withLocalDeclD `state stateType fun state => do
    let continuation ← mkAppOptM ``Sum.inl #[some stateType, some resultType, some next]
    mkLambdaFVars #[next, state] (← mkEq (mkApp step state) continuation)

def deriveTailAcc (name stepName : Name) (params : Array Lean.Expr)
    (stateType resultType : Lean.Expr) : TermElabM Lean.Expr := do
  let some _ ← getFunIndInfo? false false name
    | throwError "verified_compile: {name} has no functional induction theorem"
  let relation ← tailRelation (mkConst stepName) stateType resultType
  let state ← argsTuple (params.toList.map (·, false))
  let goal ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Acc #[relation, state])
  let app ← exprToSyntax (mkAppN (mkConst name) params)
  let stepId := mkIdent stepName
  let remaining ← Tactic.run goal.mvarId! <| Tactic.evalTactic (← `(tactic|
    fun_induction $app <;>
      (refine Acc.intro _ ?_; intro next hs; simp_all [$stepId:ident])))
  unless remaining.isEmpty do
    throwError "verified_compile: the tail transition of {name} has unproved induction cases"
  let proof ← instantiateMVars goal
  if proof.hasExprMVar then
    throwError "verified_compile: the termination proof of {name} has unresolved arguments"
  return proof

def tailWellFounded (step : Lean.Expr) (params : Array Lean.Expr) (types : List Ty)
    (stateType resultType : Lean.Expr) (acc : Lean.Expr) : MetaM Lean.Expr := do
  let relation ← tailRelation step stateType resultType
  let curried ← mkLambdaFVars params acc
  let all ← withLocalDeclD `state stateType fun state => do
    let values ← argProjsE state (types.map fun _ => .borrowed) types.length
    let proof := mkAppN curried values.toArray
    mkLambdaFVars #[state] (← mkExpectedTypeHint proof (← mkAppM ``Acc #[relation, state]))
  mkAppM ``WellFounded.intro #[all]

end Verified.Reflect
