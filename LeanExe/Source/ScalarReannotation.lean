import LeanExe.Source.ScalarHead
import LeanExe.Source.ScalarTypedLiteralInstance

namespace LeanExe.Source.Scalar

/-- Source expressions related by standard arithmetic heads, standard numerals,
and metadata. The binary rule requires the same native operation on both sides;
it does not identify custom instances or different runtime operands. -/
inductive Reannotates : Lean.Expr → Lean.Expr → Prop where
  | same (expression : Lean.Expr) : Reannotates expression expression
  | binary (sourceMeaning : Head sourceHead operation)
      (targetMeaning : Head targetHead operation)
      (left : Reannotates sourceLeft targetLeft)
      (right : Reannotates sourceRight targetRight) :
      Reannotates (.app (.app sourceHead sourceLeft) sourceRight)
        (.app (.app targetHead targetLeft) targetRight)
  | numeral (sourceType targetType : ResultType)
      (sourceNumber : NaturalLiteral number sourceNumeral)
      (targetNumber : NaturalLiteral number targetNumeral)
      (sourceInstance : TypedLiteralInstance number sourceType sourceEvidence)
      (targetInstance : TypedLiteralInstance number targetType targetEvidence) :
      Reannotates (typedLiteralExpr sourceType sourceNumeral sourceEvidence)
        (typedLiteralExpr targetType targetNumeral targetEvidence)
  | metadata (related : Reannotates source target) :
      Reannotates (.mdata sourceData source) (.mdata targetData target)

theorem Reannotates.symm {source target : Lean.Expr}
    (related : Reannotates source target) : Reannotates target source := by
  induction related with
  | same expression => exact .same expression
  | binary first second left right ihl ihr => exact .binary second first ihl ihr
  | numeral first second firstNumber secondNumber firstInstance secondInstance =>
    exact .numeral second first secondNumber firstNumber secondInstance firstInstance
  | metadata _ ih => exact .metadata ih

end LeanExe.Source.Scalar
