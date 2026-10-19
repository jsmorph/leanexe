import Verified.Reflect.TailTermination
import Verified.Reflect.TailState
import Verified.Reflect.TailBounds

namespace Verified.Reflect

open Lean Meta Elab

private def containsSelf (name : Name) (e : Lean.Expr) : Bool :=
  (e.find? (·.isConstOf name)).isSome

private partial def tailCallsOnly (name : Name) (e : Lean.Expr) : MetaM Bool := do
  if !containsSelf name e then return true
  let e ← projReduce e
  if e.getAppFn.isConstOf name then
    return e.getAppArgs.all fun arg => !containsSelf name arg
  if let .letE n type value body _ := e then
    if containsSelf name value then return false
    return ← withLocalDeclD n type fun x => tailCallsOnly name (body.instantiate1 x)
  if let some app ← matchMatcherApp? e then
    if app.discrs.size == 1 && app.alts.size == 1 && app.remaining.isEmpty &&
        !app.discrInfos.any (·.hName?.isSome) && !containsSelf name app.discrs[0]! then
      return ← lambdaTelescope app.alts[0]! fun _ body => tailCallsOnly name body
    return false
  match e.getAppFnArgs with
  | (``ite, #[_, p, _, yes, no]) =>
    return !containsSelf name p && (← tailCallsOnly name yes) && (← tailCallsOnly name no)
  | (``dite, #[_, p, _, yes, no]) =>
    if containsSelf name p then return false
    let .lam _ _ y _ := yes.consumeMData | return false
    let .lam _ _ n _ := no.consumeMData | return false
    if y.hasLooseBVars || n.hasLooseBVars then return false
    return (← tailCallsOnly name y) && (← tailCallsOnly name n)
  | _ => return false

def isTailDefinition (name eqName : Name) : MetaM Bool := do
  forallTelescope (← inferType (mkConst eqName)) fun _ eqn => do
    let some (_, _, rhs) := eqn.eq? | return false
    tailCallsOnly name rhs

def reflectTailSource (base name eqName : Name) (sigs funs rest : Lean.Expr)
    (callees : List Callee) : TermElabM Reflected :=
  withRecursiveInput base name eqName fun input =>
      withLocalDeclD `k (mkConst ``Nat) fun k => do
    let ⟨params, types, rhs, resultType, resultShape, vars, ctx, env, _, M, _, _⟩ := input
    let state ← tailState name input
    let c : Ctx :=
      { base := base.getPrefix
        sigs
        funs
        callees
        vars
        ctx
        env
        tables := { sigs, prog := rest, funs, fuel := k } }
    let reflectWith (modes : List Mode) : MetaM TailReflection := do
      let sig : Sig := ⟨types, resultShape.ty, true, modes, false⟩
      let t : TailContext := ⟨name, sig, state.type, resultType, state.flatten,
        ← resultShape.fn resultType, state.meaning⟩
      reflectTailSplit t c params.toList rhs
    let mut modes := types.map fun _ => .borrowed
    let mut r ← reflectWith modes
    for _ in [0:types.length] do
      let some choice ← modesOf (← mkAppM ``TailBody.paramChoice #[r.src, modesExpr modes])
        | throwError "verified_compile: cannot infer tail parameter modes of {name}"
      if choice == modes then break
      modes := choice
      r ← reflectWith modes
    addDefinition (base ++ `body) (← inferType r.src) r.src
    let body := mkConst (base ++ `body)
    let stepFn ← mkLambdaFVars params r.step
    let tupleValues (x : Lean.Expr) : MetaM (List Lean.Expr) :=
      argProjsE x (types.map fun _ => .borrowed) types.length
    let step ← withLocalDeclD `state state.type fun x => do
      let body := stepFn.beta (← tupleValues x).toArray
      let native ← fieldTerms base.getPrefix ⟨body, ← mkEqRefl body⟩
      unless ← kernelDefEq body native.term do
        throwError "verified_compile: tail state fields of {name} changed their meaning"
      mkLambdaFVars #[x] native.term
    addDefinition (base ++ `step) (← inferType step) step
    enableRealizationsForConst (base ++ `step)
    let step := mkConst (base ++ `step)
    let acc ← deriveTailAcc name (base ++ `step) params state.type resultType
    let wf ← tailWellFounded step params types state.type resultType acc
    addTheorem (base ++ `wellFounded) (← inferType wf) wf
    let wf := mkConst (base ++ `wellFounded)
    let nativeRank ← mkAppM ``Tail.rank #[step, wf]
    let rank ← withLocalDeclD `funs (mkApp (mkConst ``Funs) sigs) fun fs => do
      withLocalDeclD `env (mkApp (mkConst ``Env) ctx) fun e => do
        mkLambdaFVars #[fs, e] (mkApp nativeRank (state.unflatten.beta #[e]))
    let placed ← mkAppM ``TailBody.placeArgs
      #[modesExpr modes, modesExpr (paramModes types modes), body]
    let func ← mkAppOptM ``TailFunc.mk #[some sigs, some (toExpr name.getString!), some ctx,
      some (tyExpr resultShape.ty), some (modesExpr modes), some body,
      some (← evalEq placed (boolConst true)), some rank]
    addDefinition (base ++ `func) (mkApp (mkConst ``TailFunc) sigs) func
    let ψ ← resultShape.fn resultType
    let denote ← mkAppM ``TailBody.denote #[funs, body]
    let nativeProof ← mkLambdaFVars params r.proof
    let commute ← withLocalDeclD `state state.type fun x => do
      let h := mkAppN nativeProof (← tupleValues x).toArray
      let rhs ← mkAppM ``Sum.map #[state.flatten, ψ, mkApp step x]
      mkLambdaFVars #[x] (← mkExpectedTypeHint h
        (← mkEq (mkApp denote (state.flatten.beta #[x])) rhs))
    addTheorem (base ++ `step_eq) (← inferType commute) commute
    let nativeFixed ← transHint (mkAppN (mkConst eqName) params) r.fixed
    let nativeFixed ← mkLambdaFVars params nativeFixed
    let fixed ← withLocalDeclD `state state.type fun x => do
      let h := mkAppN nativeFixed (← tupleValues x).toArray
      let out ← mkAppM ``Sum.elim
        #[state.meaning, ← mkAppOptM ``id #[some resultType], mkApp step x]
      mkLambdaFVars #[x] (← mkExpectedTypeHint h (← mkEq (mkApp state.meaning x) out))
    let fixed ← mkAppM ``Tail.fixed_transport
      #[state.flatten, state.unflatten, ψ, state.left, state.right, commute, state.meaning, fixed]
    addTheorem (base ++ `fixed) (← inferType fixed) fixed
    let decrease ← withLocalDeclD `state state.type fun x =>
        withLocalDeclD `next state.type fun next => do
      let transition ← mkEq (mkApp step x)
        (← mkAppOptM ``Sum.inl #[some state.type, some resultType, some next])
      withLocalDeclD `h transition fun h => do
        mkLambdaFVars #[x, next, h] (← mkAppM ``Tail.rank_lt #[wf, h])
    let decrease ← mkAppM ``Tail.decreases_transport
      #[state.flatten, state.unflatten, ψ, state.left, state.right, commute, nativeRank, decrease]
    let f := mkConst (base ++ `func)
    addTheorem (base ++ `decreases) (← mkAppM ``TailFunc.Decreases #[f, funs]) decrease
    addTheorem (base ++ `denote_eq) (← mkForallFVars params (← inferType r.proof))
      (← mkLambdaFVars params r.proof)
    let depth ← evalBool m!"whether tail function {name} takes the call depth"
      (← mkAppM ``TailFunc.depth #[func])
    let aborts ← evalBool m!"whether tail function {name} may allocate or call guarded code"
      (← mkAppM ``TailFunc.aborts #[func])
    let reflected ← finishReflected base name params types resultShape.ty resultType aborts modes depth
      (base ++ `meaning_eq)
    addTailBounds base sigs funs rest k callees input state func reflected

end Verified.Reflect
