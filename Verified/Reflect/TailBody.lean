import Verified.Reflect.Definitions
import Verified.Reflect.TailListLemmas
import Verified.Reflect.TailModes

namespace Verified.Reflect

open Lean Meta

structure TailContext where
  name : Name
  signature : Sig
  stateType : Lean.Expr
  resultType : Lean.Expr
  flattenState : Lean.Expr
  flattenResult : Lean.Expr
  meaning : Lean.Expr

structure TailReflection where
  src : Lean.Expr
  step : Lean.Expr
  fixed : Lean.Expr
  proof : Lean.Expr

def TailContext.sumType (t : TailContext) : MetaM Lean.Expr :=
  mkAppM ``Sum #[t.stateType, t.resultType]

def TailContext.outcome (t : TailContext) (step : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``Sum.elim #[t.meaning, ← mkAppOptM ``id #[some t.resultType], step]

def TailReflection.restate (r : TailReflection) (eq : Lean.Expr) : MetaM TailReflection := do
  return { r with fixed := ← transHint (← mkEqSymm eq) r.fixed }

def tailLemma (name : Name) (t : TailContext) (c : Ctx)
    (args proofs : List (Name × Lean.Expr)) (inst? : Option Lean.Expr := none) :
    MetaM Lean.Expr := do
  let app ← LemmaApp.start name
    ([(`S, c.sigs), (`Γ, c.ctx), (`params, ctxExpr t.signature.params),
      (`result, tyExpr t.signature.result), (`funs, c.funs), (`env, c.env)] ++ args)
  if let some inst := inst? then
    for (name, value) in app.names.zip app.mvars.toList do
      let type ← instantiateMVars (← inferType value)
      if type.isAppOf ``Decidable then app.assign name inst
  for (name, proof) in proofs do
    app.assign name (← mkExpectedTypeHint proof (← app.hypType name))
  app.finish

def reflectTailCondition (c : Ctx) (p inst : Lean.Expr) : MetaM Reflection := do
  let test ← mkAppOptM ``Decidable.decide #[some p, some inst]
  if let (``Eq, #[type, value, tru]) := p.consumeMData.getAppFnArgs then
    if (← whnfR type).isConstOf ``Bool && tru.isConstOf ``Bool.true then
      let r ← reflect c value
      let h ← mkAppOptM ``tail_bool_decide_true #[some value, some inst]
      return r.as (← transHint r.proof h) test
  if let some (.ne, left, right) ← comparison? p then
    let r ← reflect.reflectCmp c .ne left right
    let h ← mkAppOptM ``tail_word_decide_ne #[some left, some right, some inst]
    return r.as (← transHint r.proof h) test
  reflect c test

mutual

partial def reflectTailBody (t : TailContext) (c : Ctx) (e : Lean.Expr) :
    MetaM TailReflection := do
  let e ← projReduce e
  if e.getAppFn.isConstOf t.name then
    let args := e.getAppArgs
    unless args.size == t.signature.params.length do
      throwError "verified_compile: a continuing call of {t.name} must supply every argument"
    let bind ← (args.toList.zip t.signature.params).zipIdx.mapM fun ((a, ty), i) => do
      if ty.scalar then return false
      if t.signature.mode i == .owned then return !(← projReduce a).isFVar
      return !(← isPlace a)
    if bind.any id then
      return ← reflectTailBody t c (← bindArgs e.getAppFn args.toList bind #[] #[])
    let rs ← args.toList.mapM (reflect c)
    let nilArgs ← mkAppOptM ``Args.nil #[some c.sigs, some c.ctx]
    let argList ← rs.foldrM (fun r acc => mkAppM ``Args.cons #[r.src, acc]) nilArgs
    let nilEq ← mkAppOptM ``ofFn_nil_eq #[some c.sigs, some c.ctx, some c.funs, some c.env]
    let hargs ← rs.foldrM (fun r acc => mkAppM ``ofFn_cons_eq #[r.proof, acc]) nilEq
    let state ← argsTuple (args.toList.map (·, false))
    let step ← mkAppOptM ``Sum.inl #[some t.stateType, some t.resultType, some state]
    let src ← mkAppOptM ``TailBody.next #[some c.sigs, some (ctxExpr t.signature.params),
      some (tyExpr t.signature.result), some c.ctx, some (← mkAppM ``Args.get #[argList])]
    let proof ← tailLemma ``tail_next_eq t c
      [(`φ, t.flattenState), (`args, ← mkAppM ``Args.get #[argList]),
        (`state, state)] [(`ha, hargs)]
    return ⟨src, step, ← rflEq e (← t.outcome step), proof⟩
  if let .letE n type value body _ := e then
    if ← isPlace value then return ← reflectTailBody t c (body.instantiate1 value)
    let ty ← tyOf type
    if let .pair _ _ := ty then
      let view ← pairView c.base type
      let r ← destructureTail t c [] value fun a b => do
        return body.instantiate1 (← view.rebuild a b)
      return ← r.restate (← view.eta (Lean.mkLambda n .default type body) value)
    let rv ← reflect c value
    let shape ← shapeOf type
    return ← withLocalDeclD n type fun x => do
      let env ← mkAppOptM ``Env.cons
        #[some c.ctx, some (tyExpr ty), some (shape.apply x), some c.env]
      let c' := { c with vars := (x, ty) :: c.vars, env, ctx := consCtx ty c.ctx }
      let rb ← reflectTailSplit t c' [x] (body.instantiate1 x)
      let src ← mkAppM ``TailBody.letE #[rv.src, rb.src]
      let stepFn ← mkLambdaFVars #[x] rb.step
      let fixedFn ← mkLambdaFVars #[x] rb.fixed
      let proofFn ← mkLambdaFVars #[x] rb.proof
      let step := stepFn.beta #[value]
      let fixed ← mkAppM ``tail_let_fixed
        #[t.meaning, value, ← mkLambdaFVars #[x] (body.instantiate1 x), stepFn, fixedFn]
      let proof ← tailLemma ``tail_let_eq t c
        [(`φ, t.flattenState), (`ψ, t.flattenResult), (`flatten, ← shape.fn type),
          (`value, rv.src), (`body, rb.src), (`V, value), (`step, stepFn)]
        [(`hv, rv.proof), (`hb, proofFn)]
      return ⟨src, step, fixed, proof⟩
  if let some app ← matchMatcherApp? e then
    if app.discrs.size == 1 then
      if let (``List, #[el]) := (← whnfR (← inferType app.discrs[0]!)).getAppFnArgs then
        if (← whnfR el).isConstOf ``UInt64 then
          return ← reflectTailListMatch t c app
    if app.discrs.size == 1 && app.alts.size == 1 &&
        !app.discrInfos.any (·.hName?.isSome) then
      let d := app.discrs[0]!
      if (← projReduce d).isAppOf ``Prod.mk && app.altNumParams[0]! == 2 then
        let fields ← matchFields app d
        let expanded ← withLetDecl `first (← inferType fields[0]!) fields[0]! fun a => do
          withLetDecl `second (← inferType fields[1]!) fields[1]! fun b =>
            mkLetFVars #[a, b] (app.alts[0]!.beta #[a, b])
        return ← reflectTailBody t c expanded
      if let some (_, fields) ← structOf? (← inferType d) then
        let fieldsOf (x : Lean.Expr) : MetaM (Array Lean.Expr) := fields.mapM (mkProjection x)
        let expanded ← if ← isPlace d then pure (app.alts[0]!.beta (← fieldsOf d))
          else withLetDecl `value (← inferType d) d fun x => do
            mkLetFVars #[x] (app.alts[0]!.beta (← fieldsOf x))
        return ← (← reflectTailBody t c expanded).restate (← casesEq app fieldsOf)
      if let .elem _ ← tyOf (← inferType d) then
        let expanded ← if (← projReduce d).isFVar then
            pure (app.alts[0]!.beta (← matchFields app d))
          else withLetDecl `value (← inferType d) d fun x => do
            mkLetFVars #[x] (app.alts[0]!.beta (← matchFields app x))
        return ← (← reflectTailBody t c expanded).restate (← casesEq app (matchFields app))
      let r ← destructureTail t c [] d fun a b => do
        return app.alts[0]!.beta (← matchFields app (← mkAppM ``Prod.mk #[a, b]))
      return ← r.restate (← casesEq app (matchFields app))
  match e.getAppFnArgs with
  | (``dite, #[α, p, inst, yes, no]) =>
    let .lam _ _ y _ := yes.consumeMData
      | throwError "verified_compile: unsupported tail branch {yes}"
    let .lam _ _ n _ := no.consumeMData
      | throwError "verified_compile: unsupported tail branch {no}"
    if y.hasLooseBVars || n.hasLooseBVars then
      throwError "verified_compile: tail branches cannot use the condition's proof"
    reflectTailBody t c (← mkAppOptM ``ite #[some α, some p, some inst, some y, some n])
  | (``ite, #[_, p, inst, yes, no]) =>
    let rc ← reflectTailCondition c p inst
    let ry ← reflectTailBody t c yes
    let rn ← reflectTailBody t c no
    let step ← mkAppOptM ``ite
      #[some (← t.sumType), some p, some inst, some ry.step, some rn.step]
    let src ← mkAppM ``TailBody.ite #[rc.src, ry.src, rn.src]
    let fixed ← mkAppM ``tail_ite_fixed #[t.meaning, p, ry.fixed, rn.fixed]
    let proof ← tailLemma ``tail_ite_decide_eq t c
      [(`φ, t.flattenState), (`ψ, t.flattenResult), (`P, p), (`cond, rc.src),
        (`yes, ry.src), (`no, rn.src), (`Y, ry.step), (`N, rn.step)]
      [(`hc, rc.proof), (`hy, ry.proof), (`hn, rn.proof)] (some inst)
    return ⟨src, step, fixed, proof⟩
  | _ =>
    let r ← reflect c e
    let src ← mkAppOptM ``TailBody.ret #[some c.sigs, some (ctxExpr t.signature.params),
      some (tyExpr t.signature.result), some c.ctx, some r.src]
    let step ← mkAppOptM ``Sum.inr #[some t.stateType, some t.resultType, some e]
    let proof ← tailLemma ``tail_ret_eq t c
      [(`ψ, t.flattenResult), (`value, r.src), (`V, e)] [(`hv, r.proof)]
    return ⟨src, step, ← rflEq e (← t.outcome step), proof⟩

partial def reflectTailListMatch (t : TailContext) (c : Ctx) (app : MatcherApp) :
    MetaM TailReflection := do
  let xs := app.discrs[0]!
  unless (← projReduce xs).isFVar do
    let expanded ← withLetDecl `xs (← inferType xs) xs fun value =>
      mkLetFVars #[value] { app with discrs := #[value] }.toExpr
    return ← (← reflectTailBody t c expanded).restate (← bareEq expanded app.toExpr)
  unless app.remaining.isEmpty do
    throwError "verified_compile: a tail list match cannot be applied to further arguments"
  let (empty, branch, nativeEq) ← listMatcherCases app
  let (x, _) ← varOf c xs
  let hx ← bareEq (← mkAppM ``Env.get #[c.env, x]) (← flatValue xs)
  let re ← reflectTailBody t c empty
  let (node, nodeStep, nodeFixed, nodeProof) ←
    withListCaseFields c xs fun inner head tail => do
      let rn ← reflectTailBody t inner (branch.beta #[head, tail])
      return (rn.src, ← mkLambdaFVars #[head, tail] rn.step,
        ← mkLambdaFVars #[head, tail] rn.fixed, ← mkLambdaFVars #[head, tail] rn.proof)
  let step ← mkAppOptM ``List.casesOn
    #[some (mkConst ``UInt64),
      some (Lean.mkLambda `xs .default (← inferType xs) (← t.sumType)),
      some xs, some re.step, some nodeStep]
  let fixed ← mkAppM ``tail_listCase_fixed
    #[t.meaning, xs, empty, branch, re.step, nodeStep, re.fixed, nodeFixed]
  let proof ← tailLemma ``tail_listCase_eq t c
    [(`φ, t.flattenState), (`ψ, t.flattenResult), (`x, x), (`empty, re.src),
      (`node, node), (`xs, xs), (`emptyStep, re.step), (`nodeStep, nodeStep)]
    [(`hx, hx), (`he, re.proof), (`hn, nodeProof)]
  let r : TailReflection := ⟨← mkAppM ``TailBody.treeCase #[x, re.src, node], step, fixed, proof⟩
  r.restate nativeEq

partial def reflectTailSplit (t : TailContext) (c : Ctx) (xs : List Lean.Expr)
    (body : Lean.Expr) : MetaM TailReflection := do
  match xs with
  | [] => reflectTailBody t c body
  | x :: rest =>
    match ← tyOf (← inferType x) with
    | .pair _ _ =>
      let view ← pairView c.base (← inferType x)
      let r ← destructureTail t c rest x fun a b => do
        return body.replaceFVar x (← view.rebuild a b)
      return ← r.restate (← view.eta (← mkLambdaFVars #[x] body) x)
    | _ => reflectTailSplit t c rest body

partial def destructureTail (t : TailContext) (c : Ctx) (rest : List Lean.Expr)
    (value : Lean.Expr) (body : Lean.Expr → Lean.Expr → MetaM Lean.Expr) :
    MetaM TailReflection := do
  let rv ← reflect c value
  let .pair s u := rv.ty | throwError "verified_compile: {value} is not a tail-state pair"
  let view ← pairView c.base (← inferType value)
  withLocalDeclD `first view.α fun a => withLocalDeclD `second view.β fun b => do
    let envA ← mkAppOptM ``Env.cons
      #[some c.ctx, some (tyExpr s), some (← flatValue a), some c.env]
    let envB ← mkAppOptM ``Env.cons
      #[some (consCtx s c.ctx), some (tyExpr u), some (← flatValue b), some envA]
    let c' : Ctx :=
      { c with
        vars := (b, u) :: (a, s) :: c.vars
        env := envB
        ctx := consCtx u (consCtx s c.ctx) }
    let leanBody ← body a b
    let rb ← reflectTailSplit t c' (b :: a :: rest) leanBody
    let stepFn ← mkLambdaFVars #[a, b] rb.step
    let fixedFn ← mkLambdaFVars #[a, b] rb.fixed
    let proofFn ← mkLambdaFVars #[a, b] rb.proof
    let pair := view.pair value
    let step := stepFn.beta #[← mkAppM ``Prod.fst #[pair], ← mkAppM ``Prod.snd #[pair]]
    let fixed ← mkAppM ``tail_letPair_fixed
      #[t.meaning, pair, ← mkLambdaFVars #[a, b] leanBody, stepFn, fixedFn]
    let proof ← tailLemma ``tail_letPair_eq t c
      [(`φ, t.flattenState), (`ψ, t.flattenResult),
        (`flattenFirst, ← (← shapeOf view.α).fn view.α),
        (`flattenSecond, ← (← shapeOf view.β).fn view.β), (`value, rv.src),
        (`body, rb.src), (`V, pair), (`step, stepFn)]
      [(`hv, rv.proof), (`hb, proofFn)]
    return ⟨← mkAppM ``TailBody.letPair #[rv.src, rb.src], step, fixed, proof⟩

end

end Verified.Reflect
