import LeanExe.Extract.ScalarFunc
open LeanExe.Extract.Core LeanExe.Source.Scalar
namespace BooleanPropositionLetRelationProbe

def direct (x y : UInt64) : UInt64 :=
  if (let b := x == y; b = (x == 0)) then x + 7 else y + 11

def decision (x y : UInt64) : Bool :=
  decide (let b := x == y; b ≠ (x == 0))

noncomputable def relationAllowance : Nat :=
  sizeOf (.const ``Bool.toUInt64 [] : Lean.Expr) -
    sizeOf (.const ``Bool [] : Lean.Expr) - sizeOf (.const ``Ne [.succ .zero] : Lean.Expr) + 1

example : relationAllowance ≤ sizeOf ("decide" : String) := by decide
example : relationAllowance ≤ sizeOf ("ite" : String) + sizeOf (.const ``Bool [] : Lean.Expr) := by decide
example : relationAllowance ≤ sizeOf ("ite" : String) + sizeOf (.const ``UInt64 [] : Lean.Expr) := by decide
example : relationAllowance ≤ sizeOf ("dite" : String) + sizeOf (.const ``Bool [] : Lean.Expr) := by decide
example (unequal : Bool) (left right : Lean.Expr) :
    sizeOf (Lean.Expr.app (.const ``Bool.toUInt64 []) left) <
      sizeOf (booleanRelationCondition unequal left right) + relationAllowance := by
  have heads : sizeOf (.const ``Bool.toUInt64 [] : Lean.Expr) <
      sizeOf (.const ``Ne [.succ .zero] : Lean.Expr) + sizeOf (.const ``Bool [] : Lean.Expr) + relationAllowance := by decide
  have eqLarger : sizeOf (.const ``Ne [.succ .zero] : Lean.Expr) ≤
      sizeOf (.const ``Eq [.succ .zero] : Lean.Expr) := by decide
  cases unequal <;> simp [booleanRelationCondition] at * <;> omega
end BooleanPropositionLetRelationProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanPropositionLetRelationProbe.direct, `BooleanPropositionLetRelationProbe.decision] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(extractScalarFunc name none info.type value).isSome}"
