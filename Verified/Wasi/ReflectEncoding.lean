import Verified.Reflect.Definitions

namespace Verified.Wasi.Reflect

open Lean Meta Elab Command Term
open Verified.Reflect

def emitEncoding (target : Name) (moduleName : Name) : CommandElabM Unit := do
  let base := (← getCurrNamespace) ++ target
  let moduleId := mkIdent moduleName
  let parts ← match evalModule (← getEnv) (← getOptions) moduleName with
    | .ok wasmModule => match Wasm.Encoding.encodeParts wasmModule with
      | .ok parts => pure parts
      | .error message =>
        throwError "verified_compile_wasi: module {moduleName} does not encode: {message}"
    | .error message =>
      throwError "verified_compile_wasi: cannot evaluate module {moduleName}: {message}"
  let (sections, bodies, data) := parts
  let bytesTy := mkApp (mkConst ``List [.zero]) (mkConst ``UInt8)
  let bytesListTy := mkApp (mkConst ``List [.zero]) bytesTy
  let literalOptions := maxRecDepth.set (← getOptions) 100000
  liftCoreM <| withReader (fun context =>
      { context with maxRecDepth := 100000, options := literalOptions }) do
    addLiteral (base ++ `sections) bytesListTy (toExpr sections)
    addLiteral (base ++ `bodies) bytesListTy (toExpr bodies)
    addLiteral (base ++ `data) bytesTy (toExpr data)
  let sectionsId := mkIdent (base ++ `sections)
  let bodiesId := mkIdent (base ++ `bodies)
  let dataId := mkIdent (base ++ `data)
  let restId := mkIdent (target ++ `rest_ok)
  let dataOkId := mkIdent (target ++ `data_ok)
  let countId := mkIdent (target ++ `funcs_count)
  let lengthId := mkIdent (target ++ `funcs_length)
  let codesId := mkIdent (target ++ `codes_ok)
  let count := bodies.length
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $restId : Wasm.Encoding.restOk $moduleId $sectionsId = true := by
      decide +kernel))
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $dataOkId : Wasm.Encoding.dataOk $moduleId $dataId = true := by
      decide +kernel))
  elabCommand (← `(theorem $countId : ($moduleId).funcs.length = $(Lean.quote count) := by
    decide +kernel))
  elabCommand (← `(theorem $lengthId : ($moduleId).funcs.length = ($bodiesId).length := by
    decide +kernel))
  elabCommand (← `(set_option maxRecDepth 100000 in
    theorem $codesId : Wasm.Encoding.codesOk $bodiesId = true := by
      decide +kernel))
  let predicate ← `(fun k : Nat =>
    Wasm.Encoding.funcOk ($moduleId).funcs[k]! ($bodiesId)[k]! = true)
  let mut chain ← `(Wasm.Encoding.forall_lt_zero $predicate)
  for index in [0:count] do
    let functionId := mkIdent (target ++ Name.mkSimple s!"func_ok_{index}")
    elabCommand (← `(set_option maxRecDepth 100000 in
      theorem $functionId :
          Wasm.Encoding.funcOk ($moduleId).funcs[$(Lean.quote index)]!
            ($bodiesId)[$(Lean.quote index)]! = true := by
        decide +kernel))
    chain ← `(Wasm.Encoding.forall_lt_succ (P := $predicate) (n := $(Lean.quote index))
      $chain $functionId)
  let encodingId := mkIdent (target ++ `encoding)
  let encodedId := mkIdent (target ++ `encoded)
  elabCommand (← `(noncomputable def $encodingId : List UInt8 :=
    Wasm.Encoding.assemble $sectionsId $bodiesId $dataId))
  elabCommand (← `(theorem $encodedId :
      Wasm.Encoding.encode $moduleId = .ok ⟨($encodingId).toArray⟩ ∧
        ∀ function ∈ ($moduleId).funcs,
          function.locals.length ≤ Wasm.Encoding.Decoder.maxLocals :=
    Wasm.Encoding.encode_of_parts $moduleId $sectionsId $bodiesId $dataId $restId $dataOkId
      $lengthId $codesId (by rw [$countId:ident]; exact $chain)))
  let decodedId := mkIdent (target ++ `decoded)
  elabCommand (← `(theorem $decodedId :
      Wasm.Encoding.decode ⟨($encodingId).toArray⟩ = .ok $moduleId := by
    obtain ⟨success, locals⟩ := $encodedId
    exact Wasm.Encoding.decode_encode $moduleId _ locals success))
  let bytesId := mkIdent (target ++ `bytes)
  elabCommand (← `(theorem $bytesId :
      ∃ bytes, Wasm.Encoding.encode $moduleId = .ok bytes ∧
        Wasm.Encoding.decode bytes = .ok $moduleId := by
    exact ⟨_, ($encodedId).1, $decodedId⟩))

end Verified.Wasi.Reflect
