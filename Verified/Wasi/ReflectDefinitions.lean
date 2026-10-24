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

def pureOperand (context : Ctx) (value : Lean.Expr) : MetaM Verified.Reflect.Reflection := do
  let (normalized, equation) ← normalizeTables context.bindings context.tables value
  let reflected ← if normalized.isFVar then Verified.Reflect.reflect context.pure normalized
    else Verified.Reflect.reflect.reflectSplit context.pure (context.pure.vars.map Prod.fst) normalized
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

partial def effectVarAt (signatures : Lean.Expr) (index : Nat) : MetaM Lean.Expr := do
  let (``List.cons, #[_, signature, rest]) := signatures.getAppFnArgs
    | throwError "verified_compile_wasi: no effectful function {index} in {signatures}"
  if index == 0 then return mkApp2 (mkConst ``EffectVar.here) signature rest
  let inner ← effectVarAt rest (index - 1)
  let innerSignature := (← inferType inner).appArg!
  return mkApp4 (mkConst ``EffectVar.there) rest innerSignature signature inner

end Verified.Wasi.Reflect
