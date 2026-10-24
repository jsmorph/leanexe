import Verified.Reflect.Definitions
import LeanExe.Encoding.ValidityProof

namespace Verified.Wasi.Reflect

open Lean Meta Elab Command Term
open Verified.Reflect

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
    let function := wasmModule.funcs[index]!
    let some typeIndex := function.typeIdx
      | throwError "verified_compile_wasi: function {index} has no declared type index"
    let contextName := base ++ Name.mkSimple s!"valid_context_{index}"
    let bodyName := base ++ Name.mkSimple s!"valid_body_{index}"
    let bodyId := mkIdent bodyName
    liftTermElabM do
      let functionExpr ← Term.elabTerm (← `(($moduleId).funcs[$(Lean.quote index)]!)) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let functionExpr ← instantiateMVars functionExpr
      let context ← mkAppM ``Wasm.Encoding.Spec.Validity.functionContext
        #[mkConst moduleName, functionExpr]
      addLiteral contextName (mkConst ``Wasm.Encoding.Spec.Validity.Context) context
      let body ← mkAppM ``Wasm.Function.body #[functionExpr]
      let proof ← Wasm.Encoding.ValidityProof.program
        (Wasm.Encoding.Spec.Validity.functionContext wasmModule function)
        (mkConst contextName) function.body body [] function.results
      let proposition ← mkAppM ``Wasm.Encoding.Spec.Validity.Program
        #[mkConst contextName, body, ← Wasm.Encoding.ValidityProof.typesExpr [],
          ← mkAppM ``Wasm.Function.results #[functionExpr]]
      addTheorem bodyName proposition (← mkExpectedTypeHint proof proposition)
    let functionId := mkIdent (target ++ Name.mkSimple s!"valid_func_{index}")
    elabCommand (← `(set_option maxRecDepth 100000 in
      theorem $functionId :
          Wasm.Encoding.Spec.Validity.Function $moduleId ($moduleId).funcs[$(Lean.quote index)]! := by
        exact ⟨⟨$(Lean.quote typeIndex), by decide +kernel, by decide +kernel⟩,
          by unfold Wasm.Encoding.Spec.Validity.Types Wasm.Encoding.Numeric; decide +kernel,
          by decide +kernel, $bodyId⟩))
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
