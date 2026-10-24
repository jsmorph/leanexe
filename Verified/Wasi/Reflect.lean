import Verified.Wasi.ReflectDefinitions
import Verified.Wasi.EffectAnalysis

namespace Verified.Wasi.Reflect

open Lean Meta
open Verified.Reflect
open LeanExe.Wasi

partial def reflect (context : Ctx) (expression : Lean.Expr) : MetaM Reflection := do
  let expression ← projReduce expression
  let nativeType ← actionResultType (← inferType expression)
  let result ← resultShapeOf nativeType
  if let some reflected ← reflectCall? expression then return reflected
  if let .letE name type value body _ := expression then
    if (← whnfR type).isAppOf ``Action then
      return ← reflectAs (body.instantiate1 value) expression
    let first ← mkAppM ``Action.pure #[value]
    let next := Lean.mkLambda name .default type body
    return ← reflectBind first next expression
  let (function, args) := expression.getAppFnArgs
  if function == ``Action.pure || function == ``Pure.pure then
    let value := args.back!
    match result with
    | .unit =>
      let source ← mkAppOptM ``Command.unit
        #[some context.pure.sigs, some context.sigs, some context.pure.ctx]
      let equation ← mkAppM ``unit_eq #[context.pure.funs, context.funs, context.pure.env, value]
      return ← fromEquation context result expression source equation
    | .value shape =>
      let valueReflection ← pureOperand context value
      let source ← mkAppOptM ``Command.ret
        #[some context.pure.sigs, some context.sigs, some context.pure.ctx,
          some (tyExpr shape.ty), some valueReflection.src]
      let equation ← mkAppM ``ret_eq
        #[context.pure.funs, context.funs, context.pure.env, valueReflection.src,
          ← shape.fn nativeType, value, ← userProof context.pure valueReflection]
      return ← fromEquation context result expression source equation
  if function == ``Action.bind || function == ``Bind.bind then
    return ← reflectBind args[args.size - 2]! args.back! expression
  if function == ``readSome then
    let capacity := args.back!
    let reflected ← pureOperand context capacity
    let source ← mkAppOptM ``Command.read
      #[some context.pure.sigs, some context.sigs, some context.pure.ctx, some reflected.src]
    let equation ← mkAppM ``read_eq
      #[context.pure.funs, context.funs, context.pure.env, reflected.src, capacity,
        ← userProof context.pure reflected]
    return ← fromEquation context result expression source equation
  if function == ``writeStdoutSome || function == ``writeStderrSome then
    let bytes := args.back!
    let output := mkConst (if function == ``writeStdoutSome then ``Output.stdout else ``Output.stderr)
    let reflected ← pureOperand context bytes
    let hValue ← userProof context.pure reflected
    if reflected.src.isAppOf ``Expr.var then
      let sourceVar := reflected.src.getAppArgs.back!
      let source ← mkAppOptM ``Command.write
        #[some context.pure.sigs, some context.sigs, some context.pure.ctx, some output, some sourceVar]
      let equation ← mkAppM ``write_eq
        #[context.pure.funs, context.funs, context.pure.env, output, sourceVar, bytes, hValue]
      return ← fromEquation context result expression source equation
    let first ← mkAppOptM ``Command.ret
      #[some context.pure.sigs, some context.sigs, some context.pure.ctx,
        some (tyExpr .bytes), some reflected.src]
    let sourceContext := consCtx .bytes context.pure.ctx
    let sourceVar := mkApp2 (mkConst ``Var.here) (tyExpr .bytes) context.pure.ctx
    let next ← mkAppOptM ``Command.write
      #[some context.pure.sigs, some context.sigs, some sourceContext, some output, some sourceVar]
    let source ← mkAppM ``Command.bind #[first, next]
    let equation ← mkAppM ``write_value_eq
      #[context.pure.funs, context.funs, context.pure.env, output, reflected.src, bytes, hValue]
    return ← fromEquation context result expression source equation
  if function == ``LeanExe.Wasi.exit || function == ``Action.exit then
    let code := args.back!
    let reflected ← pureOperand context code
    let source ← mkAppOptM ``Command.exit
      #[some context.pure.sigs, some context.sigs, some context.pure.ctx,
        some (resultTyExpr result.ty), some reflected.src]
    let equation ← mkAppM ``exit_eq
      #[context.pure.funs, context.funs, context.pure.env, reflected.src, code,
        ← result.fn nativeType, ← userProof context.pure reflected]
    return ← fromEquation context result expression source equation
  match function, args with
  | ``cond, #[_, condition, yes, no] =>
    return ← reflectBranch condition yes no none expression
  | ``ite, #[_, proposition, decision, yes, no] =>
    let condition ← mkAppOptM ``Decidable.decide #[some proposition, some decision]
    return ← reflectBranch condition yes no (some (proposition, decision)) expression
  | ``dite, #[type, proposition, decision, yes, no] =>
    let .lam _ _ yesBody _ := yes.consumeMData
      | throwError "verified_compile_wasi: unsupported conditional {expression}"
    let .lam _ _ noBody _ := no.consumeMData
      | throwError "verified_compile_wasi: unsupported conditional {expression}"
    if yesBody.hasLooseBVars || noBody.hasLooseBVars then
      throwError "verified_compile_wasi: conditional branches use the proof of {proposition}"
    let normalized ← mkAppOptM ``ite
      #[some type, some proposition, some decision, some yesBody, some noBody]
    return ← reflectAs normalized expression
  | ``LeanExe.Wasi.loop, #[type, count, initial, test, step] =>
    return ← reflectLoop type count initial test step expression
  | _, _ =>
    if let .const name _ := expression.getAppFn then
      if Lean.Compiler.hasInlineAttribute (← getEnv) name then
        if let some unfolded ← unfoldDefinition? expression then
          return ← reflectAs unfolded.headBeta expression
    throwError "verified_compile_wasi: unsupported action {expression}"
where
  reflectAs (normalized original : Lean.Expr) : MetaM Reflection := do
    let reflected ← reflect context normalized
    checkedReflection context reflected.result original reflected.src reflected.proof

  reflectBind (firstNative nextNative original : Lean.Expr) : MetaM Reflection := do
    let first ← reflect context firstNative
    let firstType ← actionResultType (← inferType firstNative)
    withResultValue context first.result firstType fun value bodyContext => do
      let next ← reflect bodyContext (nextNative.beta #[value])
      if next.src.containsFVar value.fvarId! then
        throwError "verified_compile_wasi: an action binding escaped its source context"
      let nextProof ← mkLambdaFVars #[value] next.proof
      let source ← mkAppM ``Command.bind #[first.src, next.src]
      let resultType ← actionResultType (← inferType original)
      let proof ← mkAppM ``bind_rel
        #[context.pure.funs, context.funs, context.pure.env, first.src, next.src,
          firstNative, nextNative, ← first.result.fn firstType, ← next.result.fn resultType,
          first.proof, nextProof]
      checkedReflection context next.result original source proof

  reflectBranch (condition yesNative noNative : Lean.Expr)
      (proposition : Option (Lean.Expr × Lean.Expr)) (original : Lean.Expr) : MetaM Reflection := do
    let conditionReflection ← pureOperand context condition
    let yes ← reflect context yesNative
    let no ← reflect context noNative
    let source ← mkAppM ``Command.ite #[conditionReflection.src, yes.src, no.src]
    let nativeType ← actionResultType (← inferType original)
    let flatten ← yes.result.fn nativeType
    let hCondition ← userProof context.pure conditionReflection
    let proof ← match proposition with
      | none =>
        mkAppM ``ite_rel
          #[context.pure.funs, context.funs, context.pure.env, conditionReflection.src,
            yes.src, no.src, condition, yesNative, noNative, flatten, hCondition, yes.proof, no.proof]
      | some (predicate, decision) =>
        mkAppM ``ite_prop_rel
          #[context.pure.funs, context.funs, context.pure.env, conditionReflection.src,
            yes.src, no.src, predicate, decision, yesNative, noNative, flatten,
            hCondition, yes.proof, no.proof]
    checkedReflection context yes.result original source proof

  reflectLoop (type count initial testNative stepNative original : Lean.Expr) : MetaM Reflection := do
    let shape ← shapeOf type
    let countReflection ← pureOperand context count
    let initialReflection ← pureOperand context initial
    withLoopState context type shape fun index state callbackContext => do
      let test ← pureOperand callbackContext (testNative.beta #[index, state])
      let step ← reflect callbackContext (stepNative.beta #[index, state])
      if test.src.containsFVar index.fvarId! || test.src.containsFVar state.fvarId! ||
          step.src.containsFVar index.fvarId! || step.src.containsFVar state.fvarId! then
        throwError "verified_compile_wasi: a loop callback escaped its source context"
      let testProof ← mkLambdaFVars #[index, state] (← userProof callbackContext.pure test)
      let stepProof ← mkLambdaFVars #[index, state] step.proof
      let source ← mkAppM ``Command.loop #[countReflection.src, initialReflection.src, test.src, step.src]
      let proof ← mkAppM ``loop_rel
        #[context.pure.funs, context.funs, context.pure.env, countReflection.src, initialReflection.src,
          test.src, step.src, count, initial, testNative, stepNative, ← shape.fn type,
          ← userProof context.pure countReflection, ← userProof context.pure initialReflection,
          testProof, stepProof]
      checkedReflection context (.value shape) original source proof

  reflectCall? (expression : Lean.Expr) : MetaM (Option Reflection) := do
    let .const name _ := expression.getAppFn | return none
    let some index := context.callees.findIdx? (·.name == name) | return none
    let some callee := context.callees[index]? | return none
    let nativeArgs := expression.getAppArgs
    let tableArgs ← callee.tableNames.mapM (tableTerm context.tables)
    let args := tableArgs.toArray ++ nativeArgs
    unless args.size == callee.signature.params.length do
      throwError "verified_compile_wasi: {name} requires all {callee.signature.params.length} arguments"
    let bind ← (args.toList.zip callee.signature.params).zipIdx.mapM fun ((arg, type), index) => do
      if type.scalar then return false
      if callee.signature.mode index = .owned then return !(← projReduce arg).isFVar
      return !(← isPlace arg)
    if bind.any id then
      let visibleBind := bind.drop tableArgs.length
      return some (← reflectAs
        (← bindArgs expression.getAppFn nativeArgs.toList visibleBind #[] #[]) expression)
    let reflected ← args.toList.mapM (pureOperand context)
    let sourceBind ← (reflected.zip callee.signature.params).zipIdx.mapM fun ((arg, type), index) => do
      if type.scalar then return false
      if callee.signature.mode index = .owned then return !arg.src.isAppOf ``Expr.var
      return !(← evalBool m!"argument placement for {name}" (← mkAppM ``Expr.isPlace #[arg.src]))
    if sourceBind.any id then
      if (sourceBind.take tableArgs.length).any id then
        throwError "verified_compile_wasi: hidden table arguments of {name} are not borrowed places"
      return some (← reflectAs (← bindArgs expression.getAppFn nativeArgs.toList
        (sourceBind.drop tableArgs.length) #[] #[]) expression)
    let nilArgs ← mkAppOptM ``Args.nil #[some context.pure.sigs, some context.pure.ctx]
    let sourceArgs ← reflected.foldrM (fun arg rest => mkAppM ``Args.cons #[arg.src, rest]) nilArgs
    let nilProof ← mkAppOptM ``ofFn_nil_eq
      #[some context.pure.sigs, some context.pure.ctx, some context.pure.funs, some context.pure.env]
    let argsProof ← reflected.foldrM
      (fun arg rest => do mkAppM ``ofFn_cons_eq #[← userProof context.pure arg, rest]) nilProof
    let values ← envExpr (args.toList.zip callee.signature.params)
    let sourceVar ← effectVarAt context.sigs index
    let sourceArgs ← mkAppM ``Args.get #[sourceArgs]
    let source ← mkAppM ``Command.call #[sourceVar, sourceArgs]
    let nativeType ← actionResultType (← inferType expression)
    let shape ← resultShapeOf nativeType
    let calleeProof := mkAppN (mkConst callee.meaning) nativeArgs
    let expected ← mkAppM ``Action.Rel
      #[← graphExpr shape nativeType, expression, ← mkAppM ``EffectFuns.get #[context.funs, sourceVar, values]]
    let calleeProof ← mkExpectedTypeHint calleeProof expected
    let proof ← mkAppM ``call_rel
      #[context.pure.funs, context.funs, context.pure.env, sourceVar, sourceArgs, values,
        expression, ← shape.fn nativeType, argsProof, calleeProof]
    return some (← checkedReflection context shape expression source proof)

end Verified.Wasi.Reflect
