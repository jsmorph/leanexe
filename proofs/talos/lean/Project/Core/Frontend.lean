import LeanExe.Core.Extract
import Project.Core.Compiler
import Project.Core.MemoryCompiler

namespace Project.Core.Frontend

open Lean Meta Elab

private def definition (name : Name) (value : Expr) : TermElabM Unit := do
  let type ← inferType value
  addAndCompile <| .defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

private def theoremAlias (name : Name) (value : Expr) : TermElabM Unit := do
  let type ← inferType value
  addAndCompile <| .thmDecl { name, levelParams := [], type, value }

/-- Compile an ordinary Lean definition to a named Talos Module. The adjacent
`correct`, `valid` and `ready` theorems refer to this exact module. -/
private def emit (stateful : Bool) (sourceName moduleName : Name)
    (exportName : String) : TermElabM Unit := do
  let certificateName := moduleName ++ `certificate
  if stateful then
    LeanExe.Core.Extract.certifyMemory sourceName certificateName
  else
    LeanExe.Core.Extract.certify sourceName certificateName
  let compiler := mkIdent (if stateful then ``Project.Core.compileMemory else ``Project.Core.compileNative)
  let term ← `(term| ($compiler:ident $(mkIdent certificateName):ident
    $(quote exportName)).toOption.get (by decide))
  let compiled ← Term.withoutErrToSorry <| Term.elabTerm term none
  Term.synthesizeSyntheticMVarsNoPostponing
  let compiled ← instantiateMVars compiled
  if compiled.hasSorry || compiled.hasMVar then
    throwError "Could not prove the module checks for {sourceName}"
  let compiledName := moduleName ++ `compiled
  definition compiledName compiled
  let structureName := if stateful then ``MemoryCompiled else ``Compiled
  let result := mkConst compiledName
  definition moduleName (mkProj structureName 0 result)
  definition (moduleName ++ `entry) (mkProj structureName 1 result)
  theoremAlias (moduleName ++ `valid) (mkProj structureName 2 result)
  theoremAlias (moduleName ++ `ready) (mkProj structureName 3 result)
  theoremAlias (moduleName ++ `correct) (mkProj structureName 4 result)
  logInfo m!"Produced Talos module {moduleName} with native correctness, validity and encoder readiness."

def compile (sourceName moduleName : Name) (exportName : String := "main") : TermElabM Unit :=
  emit false sourceName moduleName exportName

def compileState (sourceName moduleName : Name) (exportName : String := "main") : TermElabM Unit :=
  emit true sourceName moduleName exportName

end Project.Core.Frontend
