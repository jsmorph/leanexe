import LeanExe.Source.ScalarLiteralEvaluation
import LeanExe.Source.ScalarReannotation

namespace LeanExe.Source.Scalar

theorem EvalWith.metadata_inv {data : Lean.MData} {source : Lean.Expr}
    {values : List Value} {value : UInt64}
    (evaluation : EvalWith (.mdata data source) values value) :
    EvalWith source values value := by
  cases evaluation
  assumption

/-- Changing only standard arithmetic annotations preserves source evaluation. -/
theorem Reannotates.eval {source target : Lean.Expr}
    (related : Reannotates source target)
    {values : List Value} {value : UInt64}
    (evaluation : EvalWith source values value) : EvalWith target values value := by
  induction related generalizing values value with
  | same => exact evaluation
  | binary sourceMeaning targetMeaning left right ihl ihr =>
    obtain ⟨x, y, hx, hy, rfl⟩ := evaluation.binary_inv sourceMeaning
    exact .binary targetMeaning (ihl hx) (ihr hy)
  | numeral sourceType targetType sourceNumber targetNumber sourceInstance targetInstance =>
    rw [EvalWith.typedLiteral_inv sourceNumber evaluation]
    exact .ofNatTyped targetNumber targetInstance
  | metadata related ih => exact .metadata (ih evaluation.metadata_inv)

theorem Reannotates.eval_iff {source target : Lean.Expr}
    (related : Reannotates source target) {values : List Value} {value : UInt64} :
    EvalWith source values value ↔ EvalWith target values value :=
  ⟨related.eval, related.symm.eval⟩

end LeanExe.Source.Scalar
