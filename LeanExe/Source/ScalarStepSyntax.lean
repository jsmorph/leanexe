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

def yieldDirect (value : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``ForInStep.yield [.zero]) (.const ``UInt64 [])) value

def doneDirect (value : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``ForInStep.done [.zero]) (.const ``UInt64 [])) value

def branch (op : Comparison) (type : ResultType) (a b onTrue onFalse : Lean.Expr) : Lean.Expr :=
  Range.branch (resultType type) (op.condition a b) (op.evidence a b) onTrue onFalse

def idRun (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``Id.run [.zero]) (resultType .word)) body

def idPure (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero])))) (resultType .word)) body

def bindResult (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) (resultType .word)) (resultType .word)) value)
    (.lam name (resultType .word) body bi)

end LeanExe.Source.Scalar.Step
