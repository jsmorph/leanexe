# Editorial clarification evidence

The accepted report's four remarks concern terminology and paragraph wording.  The replacement preserves its mathematical propositions and source-audit status.

The excluded declaration list is `Extract.Types.nonRuntimeEvidenceTypeNames`, immediately followed by `className` and `isRuntimeStructure`.  Fuel recursion dispatch tests the first element of `sig.params` against `.nat`, then `extractNatRecFunc` uses parameter zero as the loop fuel and carries `params.drop 1`.  Explicit release checking uses `validateModuleReleases`, already described in the allocator subsection.

The [source excerpts](source-excerpts.md) include both declarations named `exportSection` found in the binary-emission file.  The report's library export-name finding uses the `CoreWasm.exportSection` declaration at line 4148.  The earlier declaration at line 77 belongs to the validator path and supplies no evidence for that finding.

## LeanExe/Extract/Types.lean

```text
240: def nonRuntimeEvidenceTypeNames : List Name :=
241:   [``Inhabited, ``Decidable, ``BEq, ``LT, ``LE, ``OfNat, ``HAdd, ``HSub, ``HMul, ``HDiv,
242:     ``HMod, ``GetElem, ``GetElem?]
243: 
244: def importedClassName (env : Environment) (name : Name) : Bool :=
245:   env.allImportedModuleNames.any fun moduleName =>
246:     match env.getModuleIdx? moduleName with
247:     | some idx =>
248:         let entries :=
249:           PersistentEnvExtension.getModuleEntries classExtension env idx (level := .private)
250:         entries.any fun entry => entry.name == name
251:     | none => false
252: 
253: def className (env : Environment) (name : Name) : Bool :=
254:   isClass env name || importedClassName env name
255: 
256: def isRuntimeStructure (env : Environment) (name : Name) : Bool :=
257:   isStructure env name && !className env name && !nonRuntimeEvidenceTypeNames.contains name
```

## LeanExe/Extract/Core.lean

```text
6862: def extractNatRecFunc
6863:     (ctx : Context)
6864:     (name : Name)
6865:     (params : List Ty)
6866:     (resultTy : Ty)
6867:     (value : Expr)
6868:     (exportName : Option String) : Except String IRFunc := do
6869:   let sourceParamCount := params.length
6870:   let useAbi := exportName.isSome
6871:   let wasmParamCount := functionParamCount useAbi params
6872:   let carriedParams := params.drop 1
```

## LeanExe/Extract/Core.lean

```text
7018:   let exportName ←
7019:     if exportEntry && name == entry then
7020:       let candidate := shortExportName name
7021:       if reservedExportNames.contains candidate then
7022:         .error s!"entry export name is reserved by the runtime ABI: {candidate}"
7023:       else
7024:         .ok (some candidate)
7025:     else
7026:       .ok none
7027:   match sig.params with
7028:   | .nat :: _ =>
7029:       if containsConstantInExpr ``Nat.brecOn value then
7030:         extractNatRecFunc ctx name sig.params sig.result value exportName
7031:       else
7032:         extractPlainFunc ctx name sig.params sig.result value exportName
```
