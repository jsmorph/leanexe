import Verified.Reflect.Definitions

namespace Verified.Reflect

open Lean Meta

partial def sourceExprEq (left right : Lean.Expr) : MetaM Lean.Expr := do
  if ← kernelDefEq left right then return ← rflEq left right
  let type ← kernelWhnf (← inferType left)
  if let .forallE _ domain _ _ := type then
    let (``Fin, #[length]) := (← kernelWhnf domain).getAppFnArgs
      | throwError "verified_compile: source equality has a non-finite argument domain {domain}"
    let some n := natOf (← kernelWhnf length)
      | throwError "verified_compile: cannot compute the source argument count {length}"
    let P ← withLocalDeclD `i domain fun i => do
      mkLambdaFVars #[i] (← mkEq (mkApp left i) (mkApp right i))
    let all ← finiteForall n P fun i => sourceExprEq (mkApp left i) (mkApp right i)
    return ← mkAppM ``funext #[all]
  let a ← kernelWhnf left
  let b ← kernelWhnf right
  let af := a.getAppFn
  let bf := b.getAppFn
  unless af.isConst && af == bf && af.constName!.getPrefix == ``Verified.Expr do
    throwError "verified_compile: different source constructors {af} and {bf}"
  let mut args := a.getAppArgs
  let target := b.getAppArgs
  unless args.size == target.size do
    throwError "verified_compile: source constructor arities differ"
  let mut proof ← mkEqRefl a
  for i in [0:args.size] do
    if ← kernelDefEq args[i]! target[i]! then continue
    let h ← sourceExprEq args[i]! target[i]!
    let motive ← withLocalDeclD `part (← inferType args[i]!) fun x => do
      mkLambdaFVars #[x] (mkAppN af (args.set! i x))
    proof ← transHint proof (← mkCongrArg motive h)
    args := args.set! i target[i]!
  mkExpectedTypeHint proof (← mkEq left right)

end Verified.Reflect
