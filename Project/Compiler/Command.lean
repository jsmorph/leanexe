import Project.Compiler.Scalar

namespace Project.Compiler

open Lean Elab Command Meta Project.IR

/-- `leanexe_compile p := f` compiles the definition `f` and adds `p.ir`, the IR
function; `p.module`, defined as `compile p.ir` with `f`'s last name component as
the export; and `p.hints`, the compiler's hints. -/
syntax (name := leanexeCompile) "leanexe_compile " ident " := " ident : command

def addDefinition (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addAndCompile <| .defnDecl <|
    mkDefinitionValEx name [] type value (.regular 1) .safe [name]

@[command_elab leanexeCompile]
def elabLeanexeCompile : CommandElab
  | `(leanexe_compile $target := $source) => do
      let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
      let base := (← getCurrNamespace) ++ target.getId
      let exportName := sourceName.getString!
      liftTermElabM do
        let (func, hints) ← compileScalar sourceName
        addDefinition (base ++ `ir) (mkConst ``Func) (funcToExpr func)
        addDefinition (base ++ `module) (mkConst ``Wasm.Module)
          (mkApp2 (mkConst ``compile) (mkConst (base ++ `ir)) (toExpr exportName))
        addDefinition (base ++ `hints) (mkConst ``Hints) (toExpr hints)
  | _ => throwUnsupportedSyntax

end Project.Compiler
