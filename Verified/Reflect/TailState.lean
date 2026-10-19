import Verified.Reflect.TailBody

namespace Verified.Reflect

open Lean Meta

structure TailState where
  type : Lean.Expr
  flatten : Lean.Expr
  unflatten : Lean.Expr
  left : Lean.Expr
  right : Lean.Expr
  meaning : Lean.Expr

def tailState (name : Name) (input : RecursiveInput) : MetaM TailState := do
  let ⟨params, types, _, _, _, _, ctx, _, invs, _, argsAt, _⟩ := input
  let stateType ← tupleType (← params.toList.mapM inferType)
  let nativeValues (state : Lean.Expr) : MetaM (List Lean.Expr) :=
    argProjsE state (types.map fun _ => .borrowed) types.length
  let flatten ← withLocalDeclD `state stateType fun state => do
    mkLambdaFVars #[state] (← envExpr ((← nativeValues state).zip types))
  let unflatten ← withLocalDeclD `env (mkApp (mkConst ``Env) ctx) fun env => do
    mkLambdaFVars #[env] (← argsTuple ((← argsAt env).map (·, false)))
  let left ← withLocalDeclD `state stateType fun state => do
    let values ← nativeValues state
    let flat := flatten.beta #[state]
    let args ← argsAt flat
    let tupleFn ← mkLambdaFVars params (← argsTuple (params.toList.map (·, false)))
    let mut h ← mkEqRefl tupleFn
    for i in [0:types.length] do
      let hi ← match invs[i]! with
        | some inv => inv.left values[i]!
        | none => rflEq args[i]! values[i]!
      let hi ← mkExpectedTypeHint hi (← mkEq args[i]! values[i]!)
      h ← mkCongr h hi
    mkLambdaFVars #[state] (← mkExpectedTypeHint h
      (← mkEq (unflatten.beta #[flat]) state))
  let P ← withLocalDeclD `env (mkApp (mkConst ``Env) ctx) fun env => do
    mkLambdaFVars #[env] (← mkEq (flatten.beta #[unflatten.beta #[env]]) env)
  let right ← splitEnv types P fun values => do
    let env ← envOfValues types values
    let args ← argsAt env
    let mut h ← mkEqRefl (mkConst ``Env.nil)
    for i in (List.range types.length).reverse do
      let flat := (← shapeOf (← inferType params[i]!)).apply args[i]!
      let hi ← match invs[i]! with
        | some inv => inv.right values[i]!
        | none => rflEq flat values[i]!
      let hi ← mkExpectedTypeHint hi (← mkEq flat values[i]!)
      let cons := mkApp2 (mkConst ``Env.cons) (ctxExpr (types.drop (i + 1))) (tyExpr types[i]!)
      h ← mkCongr (← mkCongrArg cons hi) h
    mkExpectedTypeHint h (mkApp P env).headBeta
  let meaning ← withLocalDeclD `state stateType fun state => do
    let values ← nativeValues state
    let native := mkAppN (mkConst name) values.toArray
    mkLambdaFVars #[state] native
  return ⟨stateType, flatten, unflatten, left, right, meaning⟩

end Verified.Reflect
