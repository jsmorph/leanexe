import Verified.Reflect.Definitions
import LeanExe.Encoding.ValidityProof

namespace Verified.Wasi.Reflect

open Lean Meta Elab Command Term
open Verified.Reflect

initialize Lean.registerTraceClass `verified.wasi

private def contextExpr (context : Wasm.Encoding.Spec.Validity.Context) : MetaM Lean.Expr := do
  let list := fun (type : Lean.Expr) (values : List Lean.Expr) => values.foldr
    (fun value tail => mkApp3 (mkConst ``List.cons [.zero]) type value tail)
    (mkApp (mkConst ``List.nil [.zero]) type)
  let functions ← context.functions.mapM fun function => do
    mkAppM ``Wasm.FuncType.mk #[← Wasm.Encoding.ValidityProof.typesExpr function.params,
      ← Wasm.Encoding.ValidityProof.typesExpr function.results]
  let globals ← context.globals.mapM fun (type, mutable) => do
    mkAppM ``Prod.mk #[← Wasm.Encoding.ValidityProof.valueTypeExpr type, toExpr mutable]
  let globalType ← mkAppM ``Prod #[mkConst ``Wasm.ValueType, mkConst ``Bool]
  return ← mkAppM ``Wasm.Encoding.Spec.Validity.Context.mk #[
    list (mkConst ``Wasm.FuncType) functions,
    ← Wasm.Encoding.ValidityProof.typesExpr context.locals,
    list globalType globals,
    list (mkApp (mkConst ``List [.zero]) (mkConst ``Wasm.ValueType))
      (← context.labels.mapM Wasm.Encoding.ValidityProof.typesExpr),
    ← Wasm.Encoding.ValidityProof.typesExpr context.results,
    toExpr context.hasMemory]

def emitValidity (target : Name) (moduleName : Name) : CommandElabM Unit := do
  let wasmModule ← match evalModule (← getEnv) (← getOptions) moduleName with
    | .ok value => pure value
    | .error message =>
      throwError "verified_compile_wasi: cannot evaluate module {moduleName}: {message}"
  let base := (← getCurrNamespace) ++ target
  let moduleId := mkIdent moduleName
  let predicate ← `(fun index : Nat =>
    Wasm.Encoding.Spec.Validity.Function $moduleId ($moduleId).funcs[index]!)
  let mut chain ← `(Wasm.Encoding.forall_lt_zero $predicate)
  for index in [0:wasmModule.funcs.length] do
    trace[verified.wasi] "Validate function: {index}"
    let function := wasmModule.funcs[index]!
    let some typeIndex := function.typeIdx
      | throwError "verified_compile_wasi: function {index} has no declared type index"
    let contextName := base ++ Name.mkSimple s!"valid_context_{index}"
    let functionName := base ++ Name.mkSimple s!"valid_function_{index}"
    let codeName := base ++ Name.mkSimple s!"valid_code_{index}"
    let bodyName := base ++ Name.mkSimple s!"valid_body_{index}"
    liftTermElabM do
      trace[verified.wasi] "Body {index}: {function.body.length} instructions, {function.locals.length} locals, {((← IO.getNumHeartbeats) - (← readThe Core.Context).initHeartbeats) / 1000} used heartbeats"
      let concreteBody ← Wasm.Encoding.ValidityProof.programExpr function.body
      addLiteral codeName (mkConst ``Wasm.Program) concreteBody
      let concreteFunction := mkAppN (mkConst ``Wasm.Function.mk) #[
        ← Wasm.Encoding.ValidityProof.typesExpr function.params,
        ← Wasm.Encoding.ValidityProof.typesExpr function.locals,
        mkConst codeName, ← Wasm.Encoding.ValidityProof.typesExpr function.results,
        toExpr function.typeIdx]
      addLiteral functionName (mkConst ``Wasm.Function) concreteFunction
      let context ← contextExpr (Wasm.Encoding.Spec.Validity.functionContext wasmModule function)
      addLiteral contextName (mkConst ``Wasm.Encoding.Spec.Validity.Context) context
      let proof ← Wasm.Encoding.ValidityProof.program
        (Wasm.Encoding.Spec.Validity.functionContext wasmModule function)
        (mkConst contextName) function.body (mkConst codeName) [] function.results
      let proposition ← mkAppM ``Wasm.Encoding.Spec.Validity.Program
        #[mkConst contextName, mkConst codeName, ← Wasm.Encoding.ValidityProof.typesExpr [],
          ← Wasm.Encoding.ValidityProof.typesExpr function.results]
      addTheorem bodyName proposition (← mkExpectedTypeHint proof proposition)
      trace[verified.wasi] "Body {index} checked: {((← IO.getNumHeartbeats) - (← readThe Core.Context).initHeartbeats) / 1000} used heartbeats"
    let functionProofName := base ++ Name.mkSimple s!"valid_func_{index}"
    let functionId := mkIdent functionProofName
    let literalFunction := mkIdent functionName
    let fields := #["tag", "type", "locals", "count", "context", "code", "results", "selected"].map
      fun field => Name.mkSimple s!"valid_field_{field}_{index}"
    let names := fields.map (base ++ ·)
    let ids := fields.map fun field => mkIdent (target ++ field)
    elabCommand (← `(theorem $(ids[0]!) : ($literalFunction).typeIdx = some $(Lean.quote typeIndex) :=
      by decide +kernel))
    elabCommand (← `(theorem $(ids[1]!) : ($moduleId).types[$(Lean.quote typeIndex)]? =
        some (Wasm.Encoding.Spec.signature $literalFunction) := by decide +kernel))
    elabCommand (← `(theorem $(ids[2]!) : Wasm.Encoding.Spec.Validity.Types ($literalFunction).locals :=
      by unfold Wasm.Encoding.Spec.Validity.Types Wasm.Encoding.Numeric; decide +kernel))
    elabCommand (← `(theorem $(ids[3]!) :
        ($literalFunction).params.length + ($literalFunction).locals.length < 2 ^ 32 := by decide +kernel))
    for field in [4:8] do
      liftTermElabM do
        let original ← match field with
          | 4 => mkAppM ``Wasm.Encoding.Spec.Validity.functionContext #[mkConst moduleName, mkConst functionName]
          | 5 => mkAppM ``Wasm.Function.body #[mkConst functionName]
          | 6 => mkAppM ``Wasm.Function.results #[mkConst functionName]
          | _ => Term.elabTerm (← `(($moduleId).funcs[$(Lean.quote index)]!)) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let original ← instantiateMVars original
        let literal ← match field with
          | 4 => pure (Lean.mkConst contextName)
          | 5 => pure (Lean.mkConst codeName)
          | 6 => Wasm.Encoding.ValidityProof.typesExpr function.results
          | _ => pure (Lean.mkConst functionName)
        addTheorem names[field]! (← mkEq original literal) (← mkEqRefl literal)
    liftTermElabM do
      let resultTypes ← Wasm.Encoding.ValidityProof.typesExpr function.results
      let typed := mkAppN (Lean.mkConst ``Wasm.Encoding.ValidityProof.function_of_parts)
        (#[Lean.mkConst moduleName, Lean.mkConst functionName, Lean.mkConst contextName, Lean.mkConst codeName,
          resultTypes, mkNatLit typeIndex] ++ (names.extract 0 7).map Lean.mkConst ++ #[Lean.mkConst bodyName])
      let proof := mkAppN (Lean.mkConst ``Wasm.Encoding.ValidityProof.function_of_lookup)
        #[Lean.mkConst moduleName, mkNatLit index, Lean.mkConst functionName, Lean.mkConst names[7]!, typed]
      addTheorem functionProofName (← inferType proof) proof
    chain ← `(Wasm.Encoding.forall_lt_succ (P := $predicate) (n := $(Lean.quote index))
      $chain $functionId)
  let countId := mkIdent (target ++ `valid_funcs_count)
  elabCommand (← `(theorem $countId :
      ($moduleId).funcs.length = $(Lean.quote wasmModule.funcs.length) := by decide +kernel))
  let globalsId := mkIdent (target ++ `valid_globals)
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $globalsId : ∀ declaration ∈ ($moduleId).globals,
        Wasm.Encoding.GlobalReady declaration := by
      have accepted : ∀ declaration ∈ ($moduleId).globals,
          Wasm.Encoding.ValidityProof.checkGlobal declaration = true := by decide +kernel
      exact fun declaration member =>
        Wasm.Encoding.ValidityProof.checkGlobal_sound (accepted declaration member)))
  let validityId := mkIdent (target ++ `validity)
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $validityId : Wasm.Encoding.Spec.Validity.Module $moduleId :=
      { shape := Wasm.Encoding.shape_of_isOk $moduleId (by decide +kernel)
        types := by unfold Wasm.Encoding.Spec.Validity.Types Wasm.Encoding.Numeric; decide +kernel
        imports := Wasm.Encoding.ValidityProof.checkImports_sound (by decide +kernel)
        functions := Wasm.Encoding.ValidityProof.functions_of_indices $moduleId
          (by rw [$countId:ident]; exact $chain)
        memories := Wasm.Encoding.ValidityProof.checkMemories_sound (by decide +kernel)
        globals := $globalsId
        functionCount := by decide +kernel
        functionExports := by decide +kernel
        globalExports := by decide +kernel
        memoryExports := by decide +kernel
        distinctExports := by decide +kernel }))

end Verified.Wasi.Reflect
