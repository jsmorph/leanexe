import Verified.Wasi.ReflectProgram
import Verified.Wasi.ReflectEncoding
import Verified.Wasi.ReflectValidity
import Verified.Wasi.SyntaxCheck
import Verified.Wasi.Correct
import Verified.Wasi.ProgramInitial
import Verified.Wasi.StaticPool
import Verified.Wasi.NativeTotal
import Verified.Wasi.CommandTotal
import Verified.Wasi.Stack

namespace Verified.Wasi.Reflect

open Lean Meta Elab Command Term
open Verified.Reflect

private def isEffectful (name : Name) : MetaM Bool := do
  forallTelescopeReducing (← getConstInfo name).type fun _ result => do
    return (← whnfR result).isAppOf ``LeanExe.Wasi.Action

private def checkShortNames (names : Array Name) : CommandElabM Unit := do
  let mut seen : List String := []
  for name in names do
    let short := name.getString!
    if seen.contains short then
      throwError "verified_compile_wasi: definitions share the generated name {short}"
    seen := short :: seen

private partial def specializeTheoremAux (lemmaTerm : Lean.Expr)
    (assigned : List (Name × Lean.Expr)) (type : Lean.Expr)
    (arguments retained : Array Lean.Expr) : MetaM Lean.Expr := do
    match ← whnf type with
    | .forallE binder domain body info =>
      match assigned.lookup binder with
      | some value =>
        unless ← isDefEq (← inferType value) domain do
          throwError "verified_compile_wasi: {binder} has type {← inferType value}, expected {domain}"
        specializeTheoremAux lemmaTerm assigned (body.instantiate1 value) (arguments.push value) retained
      | none =>
        withLocalDecl binder info domain fun value =>
          specializeTheoremAux lemmaTerm assigned (body.instantiate1 value)
            (arguments.push value) (retained.push value)
    | _ => mkLambdaFVars retained (mkAppN lemmaTerm arguments)
private def specializeTheorem (name : Name) (assigned : List (Name × Lean.Expr)) : MetaM Lean.Expr := do
  let lemmaTerm ← mkConstWithFreshMVarLevels name
  specializeTheoremAux lemmaTerm assigned (← inferType lemmaTerm) #[] #[]

private def emitCompilerProofs (target : Name) (base : Name) : CommandElabM Unit := do
  let pureProgram := mkIdent (base ++ `pure ++ `program)
  let pureFuns := mkIdent (base ++ `pure ++ `funs)
  let meaning := mkIdent (base ++ `pure ++ `meaning)
  let tables := mkIdent (base ++ `pure ++ `tables)
  let wrappers := mkIdent (base ++ `pure ++ `wrappers)
  let source := mkIdent (base ++ `pure ++ `module)
  let program := mkIdent (base ++ `program)
  let wasmModule := mkIdent (base ++ `module)
  let entries := mkIdent (base ++ `entries)
  let main := mkIdent (base ++ `mainEntry)
  let pool := mkIdent (base ++ `literalPool)
  let profile := mkIdent (target ++ `profile)
  let ready := mkIdent (target ++ `ready)
  let apart := mkIdent (target ++ `pool_apart)
  let pureCovered := mkIdent (base ++ `pure_covered)
  let covered := mkIdent (base ++ `effects_covered)
  let stack := mkIdent (target ++ `stackFits)
  elabCommand (← `(theorem $stack : Verified.Wasi.StackFits $source $program
      (Verified.Wasi.entryFrameBytes $source $entries $main) := by decide +kernel))
  elabCommand (← `(theorem $profile : Verified.Wasi.Relocation.Profile $source :=
    Verified.Wasi.Relocation.checkProfile_sound (by decide +kernel)))
  elabCommand (← `(theorem $ready : Verified.Wasi.EffectProg.Ready $source $pool $program :=
    Verified.Wasi.EffectProg.checkReady_sound $program (by decide +kernel)))
  elabCommand (← `(theorem $apart :
      ∀ region ∈ ($pool).regions, LeanExe.Runtime.regionsDisjoint region Verified.Wasi.ABI.scratch := by
    exact Verified.Wasi.pool_regions_apart_scratch $pool (by decide +kernel)))
  let calls ← `(Verified.Wasi.EffectProg.correctWith $pureProgram $pureFuns $meaning $tables
    $wrappers $pool $program $entries $main $profile $pureCovered $covered $apart $ready
    Wasm.HostEnv.empty)
  elabCommand (← `(theorem $(mkIdent (target ++ `calls)) :
      Verified.Wasi.CostEffectCalls $source $wasmModule
        (Verified.Wasi.Resource.PureContext.ofProg $pureProgram $pureFuns) $program $pool := $calls))
  let initial ← `(Verified.Wasi.compileWith_initialStore $pureProgram $tables $wrappers $pool
    $program $entries $main world (by decide +kernel) (by decide +kernel))
  elabCommand (← `(theorem $(mkIdent (target ++ `initial)) {World : Type} (world : World) :
      type_of% $initial := $initial))

private def nativeEnvironment (reflected : Reflected) (params : Array Lean.Expr) : MetaM Lean.Expr := do
  let types ← params.toList.mapM fun param => do tyOf (← inferType param)
  let mut env := (← ctxEnvExpr (params.toList.zip types)).2
  for table in reflected.tables.reverse do
    let context := (← inferType env).appArg!
    env ← mkAppOptM ``Env.cons
      #[some context, some (tyExpr (.array .word)), some (mkConst table.name), some env]
  return env

private def totalExecutionProof (resourceSafe : Lean.Expr) (command? : Option Lean.Expr := none) :
    MetaM Lean.Expr := do
  forallTelescope (← inferType resourceSafe) fun binders _ => do
    let execution := mkAppN resourceSafe binders
    let existsType ← whnf (← inferType execution)
    let (runner, resultArguments) ← lambdaTelescope existsType.appArg! fun _ quantified =>
      forallTelescope quantified fun fuelBinders classification =>
        return (← mkLambdaFVars #[fuelBinders[0]!] classification.getAppArgs.back!,
          classification.getAppArgs)
    let application := match command? with
      | none => mkAppN (mkConst ``native_run_total)
          (resultArguments.extract 0 10 ++ #[runner, execution])
      | some native => mkAppN (mkConst ``command_run_total)
          #[resultArguments[0]!, resultArguments[2]!, resultArguments[8]!,
            resultArguments[9]!, runner, native, execution]
    let .forallE _ safeType _ _ ← whnf (← inferType application)
      | throwError "verified_compile_wasi: total execution lacks its host premise"
    withLocalDeclD `hostReady safeType fun hostReady =>
      mkLambdaFVars (binders.push hostReady) (mkApp application hostReady)

private def emitEntryProofs (base : Name) (state : ProgramReflection) : TermElabM Unit := do
  let pureContext ← mkAppM ``Resource.PureContext.ofProg
    #[mkConst (base ++ `pure ++ `program), mkConst (base ++ `pure ++ `funs)]
  for (reflected, index) in state.out.toList.zipIdx do
    trace[verified.wasi] "Entry proofs: {reflected.name}"
    let entry ← entryExpr state reflected.name
    let someEntry ← mkAppM ``Option.some #[entry]
    let info ← getConstInfoDefn reflected.name
    let (proof, total) ← lambdaTelescope info.value fun params _ => do
      let env ← nativeEnvironment reflected params
      let native := mkAppN (mkConst reflected.name) params
      let flatten ← reflected.result.fn reflected.nativeResult
      let related := mkAppN (mkConst reflected.meaning) params
      let assignments := [(`pureSigs, pureSignatures state.pure), (`effectSigs, state.signatures),
          (`α, reflected.nativeResult), (`source, mkConst (base ++ `pure ++ `module)),
          (`pure, pureContext), (`program, mkConst (base ++ `program)),
          (`entries, mkConst (base ++ `entries)), (`pool, mkConst (base ++ `literalPool)),
          (`index, mkNatLit index), (`entry, entry), (`selected, ← mkEqRefl someEntry),
          (`calls, mkConst (base ++ `calls)), (`args, env), (`native, native),
          (`flatten, flatten), (`related, related)]
      let execution ← specializeTheorem ``compiled_native_entry_run assignments
      let resourceSafe ← specializeTheorem ``compiled_native_entry_run
        ((`aborts, toExpr false) :: assignments)
      let total ← totalExecutionProof resourceSafe
      return (← mkLambdaFVars params execution, ← mkLambdaFVars params total)
    let functionBase := base ++ Name.mkSimple reflected.name.getString!
    addTheorem (functionBase ++ `implements) (← inferType proof) proof
    let exportProof ← specializeTheorem ``compile_entry_export
      [(`pureSigs, pureSignatures state.pure), (`effectSigs, state.signatures),
        (`source, mkConst (base ++ `pure ++ `module)), (`program, mkConst (base ++ `program)),
        (`entries, mkConst (base ++ `entries)), (`pool, mkConst (base ++ `literalPool)),
        (`index, mkNatLit index), (`entry, entry), (`selected, ← mkEqRefl someEntry)]
    addTheorem (functionBase ++ `exported) (← inferType exportProof) exportProof
    addTheorem (functionBase ++ `total) (← inferType total) total

private def emitCommandProofs (base : Name) (state : ProgramReflection) (name : Name) :
    TermElabM Unit := do
  let some reflected := state.out.find? (·.name == name)
    | throwError "verified_compile_wasi: main {name} was not reflected"
  let pureContext ← mkAppM ``Resource.PureContext.ofProg
    #[mkConst (base ++ `pure ++ `program), mkConst (base ++ `pure ++ `funs)]
  let main ← mainExpr state name
  let env ← nativeEnvironment reflected #[]
  let native := Lean.mkConst name
  let assignments := [(`pureSigs, pureSignatures state.pure), (`effectSigs, state.signatures),
    (`source, mkConst (base ++ `pure ++ `module)), (`pure, pureContext),
    (`program, mkConst (base ++ `program)), (`entries, mkConst (base ++ `entries)),
    (`main, main), (`pool, mkConst (base ++ `literalPool)), (`calls, mkConst (base ++ `calls)),
    (`args, env), (`native, native), (`related, mkConst reflected.meaning)]
  let execution ← specializeTheorem ``compiled_native_start_run assignments
  addTheorem (base ++ `start) (← inferType execution) execution
  let exported ← specializeTheorem ``compile_start_export assignments
  addTheorem (base ++ `exported) (← inferType exported) exported
  let resourceSafe ← specializeTheorem ``compiled_native_start_run
    ((`aborts, toExpr false) :: assignments)
  let total ← totalExecutionProof resourceSafe (some native)
  addTheorem (base ++ `total) (← inferType total) total

private def compileProgram (target : Ident) (sources : Array Ident) (main? : Option Ident) :
    CommandElabM Unit := do
  let names ← sources.mapM fun source => liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  if names.isEmpty then throwError "verified_compile_wasi: the definition list is empty"
  if names.toList.eraseDups.length != names.size then
    throwError "verified_compile_wasi: the definition list contains duplicates"
  let base := (← getCurrNamespace) ++ target.getId
  let classifications ← names.mapM fun name => liftTermElabM (isEffectful name)
  let pureNames := (names.zip classifications).filterMap fun (name, effectful) =>
    if effectful then none else some name
  let effectNames := (names.zip classifications).filterMap fun (name, effectful) =>
    if effectful then some name else none
  checkShortNames pureNames
  checkShortNames effectNames
  if main?.isNone then
    for name in effectNames do
      if ["alloc", "release", "allocCount", "freeCount", "memory", "__indirect_function_table"].contains
          name.getString! then
        throwError "verified_compile_wasi: {name.getString!} is a reserved module export"
  prepareRecursiveTypes pureNames
  let mut pureState : Verified.Reflect.ProgramReflection := {}
  for name in pureNames do
    trace[verified.wasi] "Reflect pure: {name}"
    pureState ← liftTermElabM (Verified.Reflect.reflectProgramFunction (base ++ `pureSources) name pureState)
  let mut state := ProgramReflection.empty pureState
  let mut selected := []
  for (name, effectful) in names.zip classifications do
    if effectful then
      trace[verified.wasi] "Reflect action: {name}"
      state ← liftTermElabM (reflectProgramFunction base name state)
      selected := selected ++ [name]
  if selected.isEmpty then
    throwError "verified_compile_wasi: the definition list has no Action definition"
  let mainName? ← main?.mapM fun main => liftCoreM <| realizeGlobalConstNoOverloadWithInfo main
  let exports := if mainName?.isSome then [] else selected
  trace[verified.wasi] "Materialize: {base}"
  discard <| liftTermElabM (materializeProgram base state exports mainName?)
  trace[verified.wasi] "Compiler proofs: {base}"
  emitCompilerProofs target.getId base
  match mainName? with
  | none => liftTermElabM (emitEntryProofs base state)
  | some name => liftTermElabM (emitCommandProofs base state name)
  trace[verified.wasi] "Validity: {base}"
  emitValidity target.getId (base ++ `module)
  let refinements := match mainName? with
    | none => state.out.flatMap fun reflected =>
        let functionBase := base ++ Name.mkSimple reflected.name.getString!
        #[functionBase ++ `implements, functionBase ++ `total]
    | some _ => #[base ++ `start, base ++ `total]
  trace[verified.wasi] "Encoding: {base}"
  emitEncoding target.getId (base ++ `module) refinements (some (base ++ `validity))

syntax (name := verifiedCompileWasi) "verified_compile_wasi " ident " := " "[" ident,* "]" : command
syntax (name := verifiedCompileWasiMain)
  "verified_compile_wasi " ident " (" &"main" " := " ident ")" " := " "[" ident,* "]" : command

@[command_elab verifiedCompileWasi]
def elabVerifiedCompileWasi : CommandElab
  | `(verified_compile_wasi $target := [$sources,*]) =>
      compileProgram target sources.getElems none
  | _ => throwUnsupportedSyntax

@[command_elab verifiedCompileWasiMain]
def elabVerifiedCompileWasiMain : CommandElab
  | `(verified_compile_wasi $target (main := $main) := [$sources,*]) =>
      compileProgram target sources.getElems (some main)
  | _ => throwUnsupportedSyntax

end Verified.Wasi.Reflect
