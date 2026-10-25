import Verified.Wasi.Reflect
import Verified.Wasi.ReflectModes
import Verified.Wasi.Program

namespace Verified.Wasi.Reflect

open Lean Meta
open Verified.Reflect

structure Reflected where
  name : Name
  function : Name
  meaning : Name
  signature : EffectSig
  nativeParams : List Lean.Expr
  nativeResult : Lean.Expr
  result : ResultShape
  tables : List StaticTable

/-- Native parameters vary in the correspondence theorem.  Hidden source parameters denote
the declared table constants, introduced as local definitions during reflection. -/
def reflectDefinition (base name : Name) (context : Ctx) (tables : List StaticTable := []) :
    MetaM Reflected := do
  let info ← getConstInfoDefn name
  unless info.levelParams.isEmpty do
    throwError "verified_compile_wasi: {name} has universe parameters"
  if ← isRecursiveDefinition name then
    throwError "verified_compile_wasi: recursive effectful definition {name} is unsupported"
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let nativeTypes ← params.toList.mapM inferType
    let types ← nativeTypes.mapM tyOf
    let nativeResult ← actionResultType (← inferType body)
    let (ctx, env) ← ctxEnvExpr (params.toList.zip types)
    let pureContext := { context.pure with
      vars := params.toList.zip types
      ctx
      env }
    withStaticTables pureContext tables fun bindings tableContext => do
      let bodyContext := { context with pure := tableContext, tables := bindings }
      let reflected ← reflect bodyContext body
      let source ← instantiateMVars reflected.src
      if source.hasExprMVar || source.hasLevelMVar || source.hasFVar then
        throwError "verified_compile_wasi: {name}'s source body remains open"
      unless ← evalBool m!"argument placement for {name}" (← mkAppM ``Command.placeArgs #[source]) do
        throwError "verified_compile_wasi: {name}'s source arguments violate placement requirements"
      let modes ← paramChoiceOf name source tables.length
      let sourceTypes := List.replicate tables.length (.array .word) ++ types
      let signature : EffectSig := ⟨name.getString!, sourceTypes, modes, reflected.result.ty⟩
      let function ← mkAppOptM ``EffectFunc.mk
        #[some context.pure.sigs, some context.sigs, some (toExpr signature.name),
          some (ctxExpr sourceTypes), some (modesExpr modes),
          some (resultTyExpr signature.result), some source]
      let functionName := base ++ `func
      let meaningName := base ++ `related
      Verified.Reflect.addDefinition functionName (← inferType function) function
      let sourceBody ← mkAppM ``EffectFunc.body #[mkConst functionName]
      let native := mkAppN (mkConst name) params
      let checked ← checkedReflection bodyContext reflected.result native sourceBody reflected.proof
      let tableLocals := bindings.toArray.map (·.term)
      let proposition ← mkLetFVars tableLocals
        (← mkForallFVars params (← meaningType bodyContext checked.result native sourceBody))
      let proof ← mkLetFVars tableLocals (← mkLambdaFVars params checked.proof)
      Verified.Reflect.addTheorem meaningName proposition proof
      return {
        name := name
        function := functionName
        meaning := meaningName
        signature := signature
        nativeParams := nativeTypes
        nativeResult := nativeResult
        result := reflected.result
        tables := tables }

def Reflected.callee (reflected : Reflected) : Callee :=
  { name := reflected.name
    signature := reflected.signature
    meaning := reflected.meaning
    tableNames := reflected.tables.map (·.name) }

end Verified.Wasi.Reflect
