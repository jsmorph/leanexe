import LeanExe.Source.ExprProofBinder
import LeanExe.Source.ExprEquality
namespace ExprProofBinderTest
def equal (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := if _h : a = b then b else !b
  flag.toUInt64 + x

def proposition (x y : UInt64) : UInt64 :=
  let flag := if _h : x < y then x == 0 else y != 0
  flag.toUInt64 + y

def nested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  let flag := if _h : a then
      if _k : a ≠ b then decide (a = b) else !b
    else if _j : x ≤ y then a == b else a != b
  flag.toUInt64

def capture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let value := if _h : flag = outer then
        (let g := fun z : UInt64 => z + x; g y) == x
      else !flag
    (if _k : value then outer else !outer).toUInt64 + x
  f (y != 0)

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    let flag ← pure (if _h : first ≠ second then !second else first)
    a := a + (if _k : flag then first else !second).toUInt64
    if flag then break
  return a
end ExprProofBinderTest

namespace ExprProofBinderTest
private def subexpressions (expression : Lean.Expr) : List Lean.Expr :=
  expression :: (match expression with
    | .app f a => subexpressions f ++ subexpressions a
    | .lam _ type body _ | .forallE _ type body _ => subexpressions type ++ subexpressions body
    | .letE _ type value body _ => subexpressions type ++ (subexpressions value ++ subexpressions body)
    | .mdata _ body | .proj _ _ body => subexpressions body
    | _ => [])
end ExprProofBinderTest

run_elab do
  let env ← Lean.getEnv
  let mut expressions : List Lean.Expr := [
    .mdata default (.bvar 2), .proj `Sample 0 (.bvar 3),
    .forallE `a (.bvar 0) (.bvar 2) .instImplicit,
    .lam `a (.bvar 2) (.bvar 1) .strictImplicit,
    .letE `a (.bvar 0) (.bvar 1) (.bvar 2) false]
  for name in [`ExprProofBinderTest.equal, `ExprProofBinderTest.proposition,
      `ExprProofBinderTest.nested, `ExprProofBinderTest.capture, `ExprProofBinderTest.range] do
    let some info := env.find? name | throwError "missing declaration"
    expressions := expressions ++ [info.type, info.value!]
  let mut positions : Nat := 0
  let mut accepted : Nat := 0
  let mut rejected : Nat := 0
  for root in expressions do
    for expression in ExprProofBinderTest.subexpressions root do
      for depth in [0, 1, 2, 7] do
        positions := positions + 1
        let lifted := LeanExe.Source.ExprProofBinder.lift depth expression
        unless LeanExe.Source.ExprEquality.same lifted (expression.liftLooseBVars depth 1) do
          throwError "checked lift differs from native Lean binder lifting at depth {depth}: {repr expression}"
        let dropped := LeanExe.Source.ExprProofBinder.drop? depth expression
        unless dropped.isSome == !(expression.hasLooseBVar depth) do
          throwError "proof-reference rejection differs from native Lean variable occurrence at depth {depth}: {repr expression}"
        match dropped with
        | none => rejected := rejected + 1
        | some body =>
          accepted := accepted + 1
          unless LeanExe.Source.ExprEquality.same body (expression.lowerLooseBVars (depth + 1) 1) do
            throwError "checked binder removal differs from native Lean lowering at depth {depth}: {repr expression}"
  Lean.logInfo m!"{positions} binder positions matched native Lean lifting and occurrence checks; {accepted} accepted removals matched native lowering; {rejected} proof references rejected"
