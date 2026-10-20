import Lean

namespace Verified.Reflect

open Lean Meta

def listMatcherCases (app : MatcherApp) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  unless app.discrs.size == 1 && !app.discrInfos.any (·.hName?.isSome) do
    throwError "verified_compile: a list match requires one discriminant"
  let d := app.discrs[0]!
  let type ← inferType d
  let .lam _ _ resultType _ := app.motive
    | throwError "verified_compile: malformed list match motive"
  if resultType.hasLooseBVars then
    throwError "verified_compile: a list match cannot have a dependent result type"
  let altTypes ← app.alts.mapM inferType
  let decls := altTypes.mapIdx fun i ty => (Name.mkSimple s!"branch{i}", ty)
  withLocalDeclsDND decls fun hs => do
    let nilValue ← mkAppOptM ``List.nil #[some (mkConst ``UInt64)]
    let .reduced empty ← reduceMatcher? { app with discrs := #[nilValue], alts := hs }.toExpr
      | throwError "verified_compile: cannot reduce the empty list branch"
    let branch ← withLocalDeclD `head (mkConst ``UInt64) fun head =>
      withLocalDeclD `tail type fun tail => do
        let value ← mkAppM ``List.cons #[head, tail]
        let .reduced node ← reduceMatcher? { app with discrs := #[value], alts := hs }.toExpr
          | throwError "verified_compile: list patterns must distinguish empty and cons"
        mkLambdaFVars #[head, tail] node
    let motive ← withLocalDeclD `xs type fun xs => mkLambdaFVars #[xs] resultType
    let primitive (xs : Lean.Expr) : MetaM Lean.Expr :=
      mkAppOptM ``List.casesOn
        #[some (mkConst ``UInt64), some motive, some xs, some empty, some branch]
    let proof ← withLocalDeclD `xs type fun xs => do
      let eq ← mkEq (← primitive xs) { app with discrs := #[xs], alts := hs }.toExpr
      let P ← mkLambdaFVars #[xs] eq
      let base ← mkExpectedTypeHint (← mkEqRefl empty) (eq.replaceFVar xs nilValue)
      let step ← withLocalDeclD `head (mkConst ``UInt64) fun head =>
        withLocalDeclD `tail type fun tail => do
          let value ← mkAppM ``List.cons #[head, tail]
          let body := branch.beta #[head, tail]
          mkLambdaFVars #[head, tail]
            (← mkExpectedTypeHint (← mkEqRefl body) (eq.replaceFVar xs value))
      let cases ← mkAppOptM ``List.casesOn
        #[some (mkConst ``UInt64), some P, some xs, some base, some step]
      let general ← mkLambdaFVars (hs.push xs) cases
      pure (mkAppN general (app.alts.push d))
    return (empty.replaceFVars hs app.alts, branch.replaceFVars hs app.alts, proof)

end Verified.Reflect
