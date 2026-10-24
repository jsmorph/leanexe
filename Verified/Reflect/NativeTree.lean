import Verified.Reflect.RecursiveLayout

namespace Verified.Reflect

open Lean Meta

/-- `casesOn` of the type at `value` with the minor premises `minors`, one for each constructor in
declaration order. -/
def RecursiveLayout.nativeCases (layout : RecursiveLayout) (motive value : Lean.Expr)
    (minors : Array Lean.Expr) : MetaM Lean.Expr :=
  mkAppOptM (layout.name ++ `casesOn) (#[some motive, some value] ++ minors.map some)

/-- The alternatives of a match on a recursive type, one for each constructor in declaration order
as a function of the constructor's fields, and the proof that `casesOn` with them equals the
match.  An alternative that covers several constructors appears once for each. -/
def treeMatcherCases (layout : RecursiveLayout) (app : MatcherApp) :
    MetaM (Array Lean.Expr × Lean.Expr) := do
  unless app.discrs.size == 1 && !app.discrInfos.any (·.hName?.isSome) do
    throwError "verified_compile: a recursive match requires one discriminant"
  let d := app.discrs[0]!
  let type ← inferType d
  let .lam _ _ resultType _ := app.motive
    | throwError "verified_compile: malformed recursive match motive"
  if resultType.hasLooseBVars then
    throwError "verified_compile: a recursive match cannot have a dependent result type"
  let altTypes ← app.alts.mapM inferType
  let decls := altTypes.mapIdx fun i ty => (Name.mkSimple s!"branch{i}", ty)
  withLocalDeclsDND decls fun hs => do
    let byCtor (k : Lean.Expr → Array Lean.Expr → MetaM Lean.Expr) : MetaM (Array Lean.Expr) :=
      layout.ctors.toArray.mapM fun (ctor, _) => do
        let info ← getConstInfoCtor ctor
        forallBoundedTelescope info.type info.numFields fun fields _ =>
          k (mkAppN (mkConst ctor) fields) fields
    let branches ← byCtor fun value fields => do
      let .reduced body ← reduceMatcher? { app with discrs := #[value], alts := hs }.toExpr
        | throwError "verified_compile: cannot reduce the recursive match at {value}"
      mkLambdaFVars fields body
    let motive ← withLocalDeclD `value type fun value => mkLambdaFVars #[value] resultType
    let proof ← withLocalDeclD `value type fun value => do
      let eq ← mkEq (← layout.nativeCases motive value branches)
        { app with discrs := #[value], alts := hs }.toExpr
      let P ← mkLambdaFVars #[value] eq
      let minors ← (byCtor fun node fields => do
        let j := layout.ctors.findIdx (·.1 == node.getAppFn.constName!)
        mkLambdaFVars fields (← mkExpectedTypeHint (← mkEqRefl (branches[j]!.beta fields))
          (eq.replaceFVar value node)))
      let split ← layout.nativeCases P value minors
      let general ← mkLambdaFVars (hs.push value) split
      pure (mkAppN general (app.alts.push d))
    return (branches.map (·.replaceFVars hs app.alts), proof)

end Verified.Reflect
