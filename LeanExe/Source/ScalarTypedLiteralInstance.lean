import LeanExe.Source.ScalarLiteralInstance
import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

/-- Standard numeral evidence whose Id layers agree with its result type. -/
inductive TypedLiteralInstance (number : Nat) : ResultType → Lean.Expr → Prop where
  | word (evidence : LiteralInstance number 0 instanceExpr) :
      TypedLiteralInstance number .word instanceExpr
  | identity (type : ResultType) (numeralMeaning : NaturalLiteral number numeral)
      (evidence : TypedLiteralInstance number type instanceExpr) :
      TypedLiteralInstance number (.identity type)
        (.app (.app (.app (.const ``Id.instOfNat [.zero]) type.expr) numeral) instanceExpr)

def typedLiteralExpr (type : ResultType) (numeral evidence : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.const ``OfNat.ofNat [.zero]) type.expr) numeral) evidence

end LeanExe.Source.Scalar
