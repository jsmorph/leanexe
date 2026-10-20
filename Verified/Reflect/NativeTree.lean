import Verified.Reflect.RecursiveLayout

namespace Verified.Reflect

open Lean Meta

def treeMatcherCases (layout : RecursiveLayout) (app : MatcherApp) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  unless app.discrs.size == 1 && !app.discrInfos.any (·.hName?.isSome) do
    throwError "verified_compile: a recursive match requires one discriminant"
  let d := app.discrs[0]!
  let type ← inferType d
  let .lam _ _ resultType _ := app.motive
    | throwError "verified_compile: malformed recursive match motive"
  if resultType.hasLooseBVars then
    throwError "verified_compile: a recursive match cannot have a dependent result type"
  let info ← getConstInfoInduct layout.name
  let ctor ← getConstInfoCtor layout.node
  let minors (empty node : Lean.Expr) : Array (Option Lean.Expr) :=
    info.ctors.toArray.map fun name => some (if name == layout.empty then empty else node)
  let casesOn (motive value empty node : Lean.Expr) : MetaM Lean.Expr :=
    mkAppOptM (layout.name ++ `casesOn) (#[some motive, some value] ++ minors empty node)
  let altTypes ← app.alts.mapM inferType
  let decls := altTypes.mapIdx fun i ty => (Name.mkSimple s!"branch{i}", ty)
  withLocalDeclsDND decls fun hs => do
    let emptyValue := mkConst layout.empty
    let .reduced empty ← reduceMatcher? { app with discrs := #[emptyValue], alts := hs }.toExpr
      | throwError "verified_compile: cannot reduce the empty recursive branch"
    let branch ← forallBoundedTelescope ctor.type ctor.numFields fun fields _ => do
      let value := mkAppN (mkConst layout.node) fields
      let .reduced node ← reduceMatcher? { app with discrs := #[value], alts := hs }.toExpr
        | throwError "verified_compile: recursive patterns must distinguish both constructors"
      mkLambdaFVars fields node
    let motive ← withLocalDeclD `value type fun value => mkLambdaFVars #[value] resultType
    let primitive (value : Lean.Expr) := casesOn motive value empty branch
    let proof ← withLocalDeclD `value type fun value => do
      let eq ← mkEq (← primitive value) { app with discrs := #[value], alts := hs }.toExpr
      let P ← mkLambdaFVars #[value] eq
      let base ← mkExpectedTypeHint (← mkEqRefl empty) (eq.replaceFVar value emptyValue)
      let step ← forallBoundedTelescope ctor.type ctor.numFields fun fields _ => do
        let node := mkAppN (mkConst layout.node) fields
        mkLambdaFVars fields (← mkExpectedTypeHint (← mkEqRefl (branch.beta fields))
          (eq.replaceFVar value node))
      let split ← casesOn P value base step
      let general ← mkLambdaFVars (hs.push value) split
      pure (mkAppN general (app.alts.push d))
    return (empty.replaceFVars hs app.alts, branch.replaceFVars hs app.alts, proof)

end Verified.Reflect
