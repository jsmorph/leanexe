import Verified.Reflect.Command
import Verified.Wasi.ReflectLemmas
import Verified.Wasi.ReflectTables

namespace Verified.Wasi.Reflect

open Lean Meta
open Verified.Reflect

inductive ResultShape where
  | unit
  | value (shape : Shape)

def ResultShape.ty : ResultShape → ResultTy
  | .unit => .unit
  | .value shape => .value shape.ty

def resultTyExpr : ResultTy → Lean.Expr
  | .unit => mkConst ``ResultTy.unit
  | .value type => mkApp (mkConst ``ResultTy.value) (tyExpr type)

def ResultShape.apply : ResultShape → Lean.Expr → Lean.Expr
  | .unit, _ => mkConst ``Unit.unit
  | .value shape, payload => shape.apply payload

def ResultShape.fn (shape : ResultShape) (nativeType : Lean.Expr) : MetaM Lean.Expr := do
  let fn ← withLocalDeclD `value nativeType fun value =>
    mkLambdaFVars #[value] (shape.apply value)
  mkExpectedTypeHint fn (← mkArrow nativeType
    (mkApp (mkConst ``ResultTy.denote) (resultTyExpr shape.ty)))

def resultShapeOf (nativeType : Lean.Expr) : MetaM ResultShape := do
  if ← isDefEq nativeType (mkConst ``Unit) then return .unit
  return .value (← shapeOf nativeType)

def actionResultType (type : Lean.Expr) : MetaM Lean.Expr := do
  let type ← whnfR type
  let (``LeanExe.Wasi.Action, #[result]) := type.getAppFnArgs
    | throwError "verified_compile_wasi: expected Action, found {type}"
  return result

def effectSigExpr (signature : EffectSig) : Lean.Expr :=
  mkApp4 (mkConst ``EffectSig.mk) (toExpr signature.name) (ctxExpr signature.params)
    (modesExpr signature.modes) (resultTyExpr signature.result)

structure Callee where
  name : Name
  signature : EffectSig
  meaning : Name
  tableNames : List Name := []

structure Ctx where
  pure : Verified.Reflect.Ctx
  sigs : Lean.Expr
  funs : Lean.Expr
  callees : List Callee := []
  bindings : List PureBinding := []
  tables : List TableBinding := []

structure Reflection where
  src : Lean.Expr
  proof : Lean.Expr
  result : ResultShape
  native : Lean.Expr

def denoteCommand (context : Ctx) (source : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``Command.denote #[context.pure.funs, context.funs, source, context.pure.env]

def graphExpr (shape : ResultShape) (nativeType : Lean.Expr) : MetaM Lean.Expr := do
  let flatType := mkApp (mkConst ``ResultTy.denote) (resultTyExpr shape.ty)
  withLocalDeclD `native nativeType fun native => withLocalDeclD `flat flatType fun flat => do
    mkLambdaFVars #[native, flat] (← mkEq flat (shape.apply native))

def meaningType (context : Ctx) (shape : ResultShape) (native source : Lean.Expr) :
    MetaM Lean.Expr := do
  let nativeType ← actionResultType (← inferType native)
  mkAppM ``LeanExe.Wasi.Action.Rel
    #[← graphExpr shape nativeType, native, ← denoteCommand context source]

def checkedReflection (context : Ctx) (shape : ResultShape) (native source proof : Lean.Expr) :
    MetaM Reflection := do
  return ⟨source, ← mkExpectedTypeHint proof (← meaningType context shape native source),
    shape, native⟩

def fromEquation (context : Ctx) (shape : ResultShape) (native source equation : Lean.Expr) :
    MetaM Reflection := do
  let nativeType ← actionResultType (← inferType native)
  let proof ← mkAppM ``LeanExe.Wasi.Action.Rel.of_map_eq
    #[← shape.fn nativeType, ← mkEqSymm equation]
  checkedReflection context shape native source proof

/-- The reflection of a pure operand, with each variable of a pair type that the operand names
destructured first, as `reflectSplit` destructures it. -/
def pureOperand (context : Ctx) (value : Lean.Expr) : MetaM Verified.Reflect.Reflection := do
  let (normalized, equation) ← normalizeTables context.bindings context.tables value
  let named := (context.pure.vars.map Prod.fst).filter fun x => normalized.containsFVar x.fvarId!
  let reflected ← if normalized.isFVar then Verified.Reflect.reflect context.pure normalized
    else Verified.Reflect.reflect.reflectSplit context.pure named normalized
  return reflected.as (← restate reflected.proof equation) value

def withResultValue {α : Type} (context : Ctx) (shape : ResultShape) (nativeType : Lean.Expr)
    (next : Lean.Expr → Ctx → MetaM α) : MetaM α :=
  withLocalDeclD `value nativeType fun value => do
    match shape with
    | .unit => next value context
    | .value sourceShape =>
      let env ← mkAppOptM ``Env.cons
        #[some context.pure.ctx, some (tyExpr sourceShape.ty),
          some (sourceShape.apply value), some context.pure.env]
      let pureContext := { context.pure with
        vars := (value, sourceShape.ty) :: context.pure.vars
        ctx := consCtx sourceShape.ty context.pure.ctx
        env }
      next value { context with pure := pureContext }

def withLoopState {α : Type} (context : Ctx) (nativeType : Lean.Expr) (shape : Shape)
    (next : Lean.Expr → Lean.Expr → Ctx → MetaM α) : MetaM α :=
  withLocalDeclD `index (mkConst ``UInt64) fun index =>
    withLocalDeclD `state nativeType fun state => do
      let indexContext := consCtx .word context.pure.ctx
      let indexEnv ← mkAppOptM ``Env.cons
        #[some context.pure.ctx, some (tyExpr .word), some index, some context.pure.env]
      let env ← mkAppOptM ``Env.cons
        #[some indexContext, some (tyExpr shape.ty), some (shape.apply state), some indexEnv]
      let pureContext := { context.pure with
        vars := (state, shape.ty) :: (index, .word) :: context.pure.vars
        ctx := consCtx shape.ty indexContext
        env }
      next index state { context with pure := pureContext }

/-- The reflection of `native` in `context`, in which `Command.letPair` first binds the components
of each variable of `xs` that has a pair type and is not a sum that holds heap values.  The
components replace the variable in `native` and are split in turn, and `inner` reflects the action
that remains.  The variable dies at the split, so the code moves an owned pair into its
components, and every later use names a component. -/
partial def splitThen (context : Ctx) (xs : List Lean.Expr) (native : Lean.Expr)
    (inner : Ctx → Lean.Expr → MetaM Reflection) : MetaM Reflection := do
  match xs with
  | [] => inner context native
  | x :: rest =>
    let type ← inferType x
    let .pair first second ← tyOf type | splitThen context rest native inner
    if ← heapSum? type then return ← splitThen context rest native inner
    let view ← pairView context.pure.base type
    let pairReflection ← Verified.Reflect.reflect context.pure x
    unless pairReflection.src.isAppOf ``Expr.var do
      throwError "verified_compile_wasi: {x} is not a variable of the context"
    let pairVar := pairReflection.src.getAppArgs.back!
    let firstShape ← shapeOf view.α
    let secondShape ← shapeOf view.β
    withLocalDeclD `a view.α fun a => withLocalDeclD `b view.β fun b => do
      let firstContext := consCtx first context.pure.ctx
      let firstEnv ← mkAppOptM ``Env.cons
        #[some context.pure.ctx, some (tyExpr first), some (firstShape.apply a),
          some context.pure.env]
      let env ← mkAppOptM ``Env.cons
        #[some firstContext, some (tyExpr second), some (secondShape.apply b), some firstEnv]
      let pureContext := { context.pure with
        vars := (b, second) :: (a, first) :: context.pure.vars
        ctx := consCtx second firstContext
        env }
      let bodyNative := native.replaceFVar x (← view.rebuild a b)
      let body ← splitThen { context with pure := pureContext } (b :: a :: rest) bodyNative inner
      if body.src.containsFVar a.fvarId! || body.src.containsFVar b.fvarId! then
        throwError "verified_compile_wasi: a component of a split escaped its source context"
      let source ← mkAppM ``Command.letPair #[pairVar, body.src]
      let nativeType ← actionResultType (← inferType native)
      let proof ← mkAppM ``letPair_rel
        #[context.pure.funs, context.funs, context.pure.env, pairVar, body.src,
          ← firstShape.fn view.α, ← secondShape.fn view.β, view.pair x,
          ← graphExpr body.result nativeType, ← mkLambdaFVars #[a, b] bodyNative,
          ← mkEqRefl (← mkAppM ``Env.get #[context.pure.env, pairVar]),
          ← mkLambdaFVars #[a, b] body.proof]
      -- The view's eta law at the identity, whose values lie in `Type`, unlike the actions.
      let identity ← withLocalDeclD `y type fun y => mkLambdaFVars #[y] y
      let eta ← mkCongrArg (← mkLambdaFVars #[x] native) (← view.eta identity x)
      checkedReflection context body.result native source (← mkAppM ``rel_eta #[proof, eta])

partial def effectVarAt (signatures : Lean.Expr) (index : Nat) : MetaM Lean.Expr := do
  let (``List.cons, #[_, signature, rest]) := signatures.getAppFnArgs
    | throwError "verified_compile_wasi: no effectful function {index} in {signatures}"
  if index == 0 then return mkApp2 (mkConst ``EffectVar.here) signature rest
  let inner ← effectVarAt rest (index - 1)
  let innerSignature := (← inferType inner).appArg!
  return mkApp4 (mkConst ``EffectVar.there) rest innerSignature signature inner

end Verified.Wasi.Reflect
