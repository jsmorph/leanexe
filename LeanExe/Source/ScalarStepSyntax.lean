import LeanExe.Source.ScalarRangeSyntax
import LeanExe.Source.ScalarComparison

namespace LeanExe.Source.Scalar.Step

/-- Exact step-result annotations, including every Id layer retained by elaboration. -/
inductive ResultAnnotation where
  | word
  | identity (inner : ResultAnnotation)
  deriving DecidableEq, Repr

def resultType : ResultAnnotation → Lean.Expr
  | .word => .app (.const ``ForInStep [.zero]) (.const ``UInt64 [])
  | .identity inner => .app (.const ``Id [.zero]) (resultType inner)

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

def branch (op : Comparison) (type : ResultAnnotation) (a b onTrue onFalse : Lean.Expr) : Lean.Expr :=
  Range.branch (resultType type) (op.condition a b) (op.evidence a b) onTrue onFalse

def idRun (type : ResultAnnotation) (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``Id.run [.zero]) (resultType type)) body

def idPure (type : ResultAnnotation) (body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero])))) (resultType type)) body

def bindWord (name : Lean.Name) (bi : Lean.BinderInfo) (type : ResultAnnotation) (value body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) (.const ``UInt64 [])) (resultType type)) value)
    (.lam name (.const ``UInt64 []) body bi)

def bindResult (name : Lean.Name) (bi : Lean.BinderInfo) (input output : ResultAnnotation) (value body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) (resultType input)) (resultType output)) value)
    (.lam name (resultType input) body bi)

end LeanExe.Source.Scalar.Step
