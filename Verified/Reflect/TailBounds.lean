import Verified.Reflect.TailState
import Verified.Reflect.TailBoundLemmas
import Verified.Reflect.SourceEq

namespace Verified.Reflect

open Lean Meta

def addTailBounds (base : Name) (sigs funs prog k : Lean.Expr) (callees : List Callee)
    (input : RecursiveInput) (state : TailState) (func : Lean.Expr) (r : Reflected) :
    MetaM Reflected := do
  let ⟨params, types, rhs, _, resultShape, vars, ctx, env, _, M, _, _⟩ := input
  let f := mkConst (base ++ `func)
  let body := mkConst (base ++ `body)
  let flags := mkApp2 (mkConst ``Prog.flags) sigs prog
  let pf ← evalBoolList m!"the tail parameter flags of {r.name}"
    (← mkAppM ``TailFunc.paidParams #[func, flags])
  let paid := pf.any id
  let cost : Name := if paid then `cost else `bound
  let fuel := if r.depth then k else mkNatLit 0
  let restB := mkAppN (mkConst ``Prog.boundsAt) #[sigs, prog, funs]
  let restF := mkAppN (mkConst ``Prog.fitsAt) #[sigs, prog, funs]
  let bounds := mkApp restB fuel
  let fits := mkApp restF fuel
  let selfSig : Sig := ⟨types, r.result, true, r.modes, false⟩
  let g := sigExpr selfSig
  let sourceSigs := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Sig) g sigs
  let sourceFuns := mkAppN (mkConst ``Funs.cons) #[sigs, g, M, funs]
  let sourceFlags := mkAppN (mkConst ``Flags.cons) #[sigs, g, toExpr pf, toExpr false, flags]
  let envType := mkApp (mkConst ``Env) ctx
  let zero ← withLocalDeclD `env envType fun e => mkLambdaFVars #[e] (mkNatLit 0)
  addDefinition (base ++ `continueCost) (← inferType zero) zero
  let selfCost := mkConst (base ++ `continueCost)
  let own ← withLocalDeclD `x r.argsType fun x =>
    mkLambdaFVars #[x] (mkApp selfCost (r.envOf x))
  addBoundDefinition (base ++ `continueBound) (← inferType own) own
  let tuple ← r.tupleOf params
  let selfEq ← rflEq (mkApp (mkConst (base ++ `continueBound)) tuple) (mkNatLit 0)
  addTheorem (base ++ `continueBound_eq)
    (← mkForallFVars params (← inferType selfEq)) (← mkLambdaFVars params selfEq)
  let trueFits ← withLocalDeclD `env envType fun e =>
    mkLambdaFVars #[e] (mkConst ``Bool.true)
  let tables : Tables :=
    { sigs, prog, funs, fuel, self := some (g, selfCost, trueFits), selfFlags := some sourceFlags }
  let self : Callee :=
    { name := r.name
      sig := selfSig
      denoteEq := base ++ `meaning_eq
      bound := { bound := base ++ `continueBound, numeralEq := some (base ++ `continueBound_eq) } }
  let c : Ctx :=
    { base := base.getPrefix
      sigs := sourceSigs
      funs := sourceFuns
      callees := self :: callees
      vars
      env
      ctx
      tables }
  let expanded ← reflect.reflectSplit c params.toList rhs
  let hp ← rflEq (← mkAppM ``Sig.params #[g]) ctx
  let hr ← rflEq (← mkAppM ``Sig.result #[g]) (tyExpr r.result)
  let expansion ← mkAppM ``TailBody.toExpr #[g, hp, hr, body]
  let expansionEq ← sourceExprEq expansion expanded.src
  let ms := modesExpr (entryModes types r.modes)
  let live := Lean.mkLambda `i .default (mkConst ``Nat) (mkConst ``Bool.false)
  let b ← expanded.bound ms (toExpr pf) live
  let bridge ← mkAppM ``TailBody.allocs_toExpr
    #[body, modesExpr r.modes, toExpr false, M, funs, flags, bounds, toExpr pf, toExpr false,
      ms, toExpr pf, env]
  let costFn ← withLocalDeclD `expr (← inferType expanded.src) fun e => do
    let a ← mkAppM ``Expr.allocs
      #[sourceFuns, sourceFlags, c.tables.table false, ms, toExpr pf, live, e, env]
    let coerce ← mkAppM ``coerceCost
      #[tyExpr r.result, ← mkAppM ``Expr.mode #[ms, e], modeExpr .owned,
        ← mkAppM ``Expr.denote #[sourceFuns, e, env]]
    mkLambdaFVars #[e] (mkApp2 natAdd a coerce)
  let bridge ← transHint bridge (← mkCongrArg costFn expansionEq)
  let (_, sum) ← eqSides bridge
  let sumArgs := sum.getAppArgs
  let allocs := sumArgs[sumArgs.size - 2]!
  let coercion := sumArgs.back!
  let args := coercion.getAppArgs
  let (C, hc) ← coerceEq base.getPrefix r.result args[1]! args[2]! args[3]! rhs
  let sumEq ← congr2 sum.appFn!.appFn! allocs b.term coercion C (some b.proof) (some hc)
  let charge ← boundOf (← transHint bridge sumEq)
  let chargeFn ← mkLambdaFVars params charge.term
  let nativeValues (x : Lean.Expr) : MetaM (List Lean.Expr) :=
    argProjsE x (types.map fun _ => .borrowed) types.length
  let nativeCharge ← withLocalDeclD `state state.type fun x => do
    mkLambdaFVars #[x] (chargeFn.beta (← nativeValues x).toArray)
  let chargeProof ← mkLambdaFVars params charge.proof
  let chargeEq ← withLocalDeclD `state state.type fun x => do
    mkLambdaFVars #[x] (mkAppN chargeProof (← nativeValues x).toArray)
  let step := mkConst (base ++ `step)
  let wf := mkConst (base ++ `wellFounded)
  let nativeRank ← mkAppM ``Tail.rank #[step, wf]
  let rankEq ← withLocalDeclD `state state.type fun x => do
    mkLambdaFVars #[x] (← mkCongrArg nativeRank (mkApp state.left x))
  let app ← LemmaApp.start ``TailFunc.bound_native
    [(`func, func), (`funs, funs), (`flags, flags), (`bounds, bounds),
      (`flatten, state.flatten), (`flattenResult, ← resultShape.fn input.resultType),
      (`step, step), (`rank, nativeRank), (`charge, nativeCharge),
      (`meaning, mkConst (base ++ `step_eq))]
  app.assign `rankEq (← mkExpectedTypeHint rankEq (← app.hypType `rankEq))
  app.assign `chargeEq (← mkExpectedTypeHint chargeEq (← app.hypType `chargeEq))
  let nativeTuple ← argsTuple (params.toList.map (·, false))
  app.assign `state nativeTuple
  let root ← app.finish
  let root ← if isNatZero charge.term then do
      let (_, term) ← eqSides root
      let args := term.getAppArgs
      let zero ← mkAppM ``Tail.costAt_zero #[step, args[args.size - 2]!, nativeTuple]
      boundOf (← transHint root zero)
    else boundOf root
  let costValue ← withLocalDeclD `frames (mkConst ``Nat) fun frames =>
      withLocalDeclD `x r.argsType fun x => do
    let entry ← if r.depth then mkAppM ``TailFunc.boundAt #[f, funs, flags, restB, frames]
      else mkAppM ``TailFunc.bound #[f, funs, flags, bounds]
    mkLambdaFVars (if r.depth then #[frames, x] else #[x]) (mkApp entry (r.envOf x))
  addBoundDefinition (base ++ cost) (← inferType costValue) costValue
  let costEq := base ++ Name.mkSimple (cost.toString ++ "_eq")
  let frames := mkApp (mkConst ``Nat.succ) k
  let equationArgs := if r.depth then #[k] ++ params else params
  let costLhs := if r.depth then mkApp2 (mkConst (base ++ cost)) frames tuple
    else mkApp (mkConst (base ++ cost)) tuple
  addEquation base.getPrefix costEq equationArgs costLhs root
  if r.depth then
    let b ← expanded.fits
    let bridge ← mkAppM ``TailBody.fits_toExpr
      #[body, modesExpr r.modes, toExpr false, M, funs, fits, env]
    let fitsFn ← withLocalDeclD `expr (← inferType expanded.src) fun e => do
      mkLambdaFVars #[e] (← mkAppM ``Expr.fits #[sourceFuns, c.tables.table true, e, env])
    let bridge ← transHint (← mkEqSymm bridge) (← mkCongrArg fitsFn expansionEq)
    let valid ← fitsOf (← transHint bridge b.proof)
    let nativeValidFn ← mkLambdaFVars params valid.term
    let nativeValid ← withLocalDeclD `state state.type fun x => do
      mkLambdaFVars #[x] (nativeValidFn.beta (← nativeValues x).toArray)
    let validProof ← mkLambdaFVars params valid.proof
    let validEq ← withLocalDeclD `state state.type fun x => do
      mkLambdaFVars #[x] (mkAppN validProof (← nativeValues x).toArray)
    let app ← LemmaApp.start ``TailFunc.fits_native
      [(`func, func), (`funs, funs), (`fits, fits), (`flatten, state.flatten),
        (`flattenResult, ← resultShape.fn input.resultType), (`step, step),
        (`rank, nativeRank), (`valid, nativeValid), (`meaning, mkConst (base ++ `step_eq))]
    app.assign `rankEq (← mkExpectedTypeHint rankEq (← app.hypType `rankEq))
    app.assign `validEq (← mkExpectedTypeHint validEq (← app.hypType `validEq))
    app.assign `state nativeTuple
    let root ← fitsOf (← app.finish)
    let value ← withLocalDeclD `frames (mkConst ``Nat) fun frames =>
        withLocalDeclD `x r.argsType fun x => do
      mkLambdaFVars #[frames, x]
        (← mkAppM ``TailFunc.fitsAt #[f, funs, restF, frames, r.envOf x])
    addBoundDefinition (base ++ `fits) (← inferType value) value
    addEquation base.getPrefix (base ++ `fits_eq) equationArgs
      (mkApp2 (mkConst (base ++ `fits)) frames tuple) root
  if paid then
    addCreditBound base r (← mkAppM ``TailFunc.sig #[func]) pf r.depth params env k vars
  return { r with
    bound? := some
      { bound := base ++ cost
        fits? := if r.depth then some (base ++ `fits) else none
        numeralEq := if !r.depth && (natOf root.term).isSome then some costEq else none
        credited? := if paid then some (base ++ `bound) else none }
    paid }

end Verified.Reflect
