import Lean
import LeanExe.Extract.Core
import Project.Pipeline.Direct
import Project.Pipeline.ToExpr

namespace Project.Pipeline

open Lean Elab Command

/-- `leanexe_module m := f` compiles the imported declaration `f` and adds the
resulting module as the definition `m : Wasm.Module`. -/
syntax (name := leanexeModule) "leanexe_module " ident " := " ident : command

@[command_elab leanexeModule]
def elabLeanexeModule : CommandElab
  | `(leanexe_module $name := $entry) => do
      let entryName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo entry
      let env ← getEnv
      let some moduleIdx := env.getModuleIdxFor? entryName
        | throwError "{entryName} must be defined in an imported module"
      let moduleName := env.header.moduleNames[moduleIdx.toNat]!
      let ir ← match LeanExe.Extract.Core.compileEnvironment env moduleName entryName with
        | .ok ir => pure ir
        | .error message => throwError message
      let module_ ← match fromIR ir with
        | .ok module_ => pure module_
        | .error message => throwError message
      let declName := (← getCurrNamespace) ++ name.getId
      liftCoreM <| addAndCompile <| .defnDecl <|
        mkDefinitionValEx declName [] (mkConst ``Wasm.Module) (toExpr module_)
          (.regular 1) .safe [declName]
  | _ => throwUnsupportedSyntax

end Project.Pipeline
