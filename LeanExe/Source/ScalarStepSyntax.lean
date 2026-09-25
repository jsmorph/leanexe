import LeanExe.Source.ScalarRangeSyntax
import LeanExe.Source.ScalarComparison

namespace LeanExe.Source.Scalar.Step

def resultType : ResultType → Lean.Expr
  | .word => .app (.const ``ForInStep [.zero]) (.const ``UInt64 [])
  | .identity => .app (.const ``Id [.zero]) (.app (.const ``ForInStep [.zero]) (.const ``UInt64 []))

def doneValue (value : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero]))))
    (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])))
    (.app (.app (.const ``ForInStep.done [.zero]) (.const ``UInt64 [])) value)

def branch (op : Comparison) (type : ResultType) (a b onTrue onFalse : Lean.Expr) : Lean.Expr :=
  Range.branch (resultType type) (op.condition a b) (op.evidence a b) onTrue onFalse

end LeanExe.Source.Scalar.Step
