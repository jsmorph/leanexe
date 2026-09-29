import Project.Compiler.Scalar

namespace Project.Compiler

open Lean Elab Command Meta Project.IR

/-- `leanexe_compile p := f` compiles the definition `f` and adds `p.ir`, the IR
function; `p.module`, defined as `compile [(p.ir, name)]` with `f`'s last name
component as the export name, so `f` is function 3; and `p.hints`, the
compiler's hints. -/
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
      let funcEntry := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Func)
        (mkConst ``String)
      liftTermElabM do
        let (func, hints) ← compileDefinition sourceName
        addDefinition (base ++ `ir) (mkConst ``Func) (funcToExpr func)
        let entry := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Func)
          (mkConst ``String) (mkConst (base ++ `ir)) (toExpr exportName)
        let entries := mkApp3 (mkConst ``List.cons [Level.zero]) funcEntry entry
          (mkApp (mkConst ``List.nil [Level.zero]) funcEntry)
        addDefinition (base ++ `module) (mkConst ``Wasm.Module) (mkApp (mkConst ``compile) entries)
        addDefinition (base ++ `hints) (mkConst ``Hints) (toExpr hints)
  | _ => throwUnsupportedSyntax

end Project.Compiler
