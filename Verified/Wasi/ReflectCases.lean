import Verified.Wasi.Reflect

namespace Verified.Wasi.ReflectCases

open Lean Meta
open LeanExe LeanExe.Wasi LeanExe.Pipeline

def unit : Action Unit := pure ()

def readWrite : Action WriteResult := do
  let result ← readSome 3
  writeStdoutSome result.bytes

def discardRead : Action Unit := do
  let _ ← readSome 1
  pure ()

def namedAction : Action Unit :=
  let action := readSome 1
  do
    let _ ← action
    pure ()

def exitCase : Action Unit := LeanExe.Wasi.exit 7

def pureByteLet : Action WriteResult := do
  let bytes := bytes![65, 0, 255]
  writeStderrSome bytes

def branch : Action WriteResult := do
  let result ← readSome 2
  if result.errno == 0 then writeStdoutSome result.bytes else writeStderrSome bytes![]

def wordLoop : Action UInt64 :=
  LeanExe.Wasi.loop 3 0 (fun index _ => decide (index < 2))
    (fun index state => pure (state + index + 1))

structure State where
  count : UInt64
  bytes : LeanExe.Bytes

instance : Flat State (UInt64 × LeanExe.Bytes) := ⟨fun state => (state.count, state.bytes)⟩

def recordLoop : Action State :=
  LeanExe.Wasi.loop 3 (State.mk 0 bytes![65, 0, 255])
    (fun index state => decide (index < 3) && decide (state.count < 100))
    (fun index state => do
      let _ ← writeStdoutSome state.bytes
      pure { state with count := state.count + index + 1 })

def helper : Action WriteResult := writeStdoutSome bytes![]

def throughHelper : Action Unit := do
  let _ ← helper
  pure ()

def actionEscape (callback : UInt64 → Action Unit) : Action Unit := callback 0

private def emptyContext (base : Name) : Reflect.Ctx :=
  let sigs := Verified.Reflect.listExpr (mkConst ``Sig) []
  let funs := mkConst ``Funs.nil
  let prog := mkConst ``Prog.nil
  { pure :=
      { base, sigs, funs, callees := [], vars := [], ctx := Verified.Reflect.ctxExpr [],
        env := mkConst ``Env.nil, tables := { sigs, funs, prog, fuel := mkNatLit 0 } }
    sigs := Verified.Reflect.listExpr (mkConst ``EffectSig) []
    funs := mkConst ``EffectFuns.nil }

private def check (context : Reflect.Ctx) (name : Name) : MetaM Reflect.Reflection := do
  let info ← getConstInfoDefn name
  let reflected ← Reflect.reflect context info.value
  let sourceName := name ++ `source
  Verified.Reflect.addDefinition sourceName (← inferType reflected.src) reflected.src
  let source := mkConst sourceName
  let native := mkConst name
  let checked ← Reflect.checkedReflection context reflected.result native source reflected.proof
  Verified.Reflect.addTheorem (name ++ `related)
    (← Reflect.meaningType context checked.result native source) checked.proof
  return checked

run_meta do
  let context := emptyContext `Verified.Wasi.ReflectCases
  for name in [``unit, ``readWrite, ``discardRead, ``namedAction, ``exitCase,
      ``pureByteLet, ``branch, ``wordLoop, ``recordLoop] do
    discard (check context name)

run_meta do
  let context := emptyContext `Verified.Wasi.ReflectCases
  let reflected ← check context ``helper
  let signature : EffectSig :=
    ⟨"helper", [], [], .value (.elem (.prod .word .word))⟩
  let signatures := Verified.Reflect.listExpr (mkConst ``EffectSig) [Reflect.effectSigExpr signature]
  let body ← Reflect.denoteCommand context reflected.src
  let function ← withLocalDeclD `env (mkApp (mkConst ``Env) (Verified.Reflect.ctxExpr [])) fun env =>
    mkLambdaFVars #[env] body
  let constructor ← Verified.Reflect.LemmaApp.start ``EffectFuns.cons
    [(`signature, Reflect.effectSigExpr signature), (`function, function), (`rest, context.funs)]
  let funs ← constructor.finish
  let callerContext : Reflect.Ctx := { context with
    sigs := signatures
    funs
    callees := [{ name := ``helper, signature := signature, meaning := ``helper ++ `related }] }
  discard (check callerContext ``throughHelper)

run_meta do
  let context := emptyContext `Verified.Wasi.ReflectCases
  let rejected ← try
      let info ← getConstInfoDefn ``actionEscape
      lambdaTelescope info.value fun _ body => discard (Reflect.reflect context body)
      pure false
    catch
    | exception@(.error _ message) =>
      let text ← message.toString
      if text.startsWith "verified_compile_wasi: unsupported action" &&
          (text.splitOn "callback").length > 1 then
        pure true
      else
        throw exception
    | exception => throw exception
  unless rejected do throwError "expected rejection of an action callback parameter"

end Verified.Wasi.ReflectCases
