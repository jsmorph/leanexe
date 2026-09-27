import LeanExe.Extract.ScalarFunc
open LeanExe.Extract.Core LeanExe.Source.Scalar
namespace BooleanPropositionRelationProbe

def combined (left right : Bool) : Id (Id Bool) :=
  pure (pure (decide (left = right ∨ ¬ left)))
def mixed (left right : Bool) : UInt64 :=
  if left ≠ right ∧ left then 7 else 11

def relation (unequal : Bool) (left right : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.const (if unequal then ``Ne else ``Eq) [.succ .zero])
    (.const ``Bool [])) left) right

example (left right : Lean.Expr) :
    sizeOf (Lean.Expr.app (.const ``Bool.toUInt64 []) left) <
      sizeOf (relation false left right) + guardOperandOverhead := by
  have names : sizeOf ("True" : String) ≤ sizeOf ("Eq" : String) + 3 := by decide
  simp [relation, guardOperandOverhead] at *
  omega

example (left right : Lean.Expr) :
    sizeOf (Lean.Expr.app (.const ``Bool.toUInt64 []) right) <
      sizeOf (relation true left right) + guardOperandOverhead := by
  have names : sizeOf ("True" : String) ≤ sizeOf ("Ne" : String) + 3 := by decide
  simp [relation, guardOperandOverhead] at *
  omega
end BooleanPropositionRelationProbe

run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanPropositionRelationProbe.combined, `BooleanPropositionRelationProbe.mixed] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(extractScalarFunc name none info.type value).isSome}"
