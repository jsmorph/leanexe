import Lean

namespace LeanExe.Source.Scalar

/-- Scalar result annotations retain every Id layer present in elaborated syntax. -/
inductive ResultType where
  | word
  | identity (inner : ResultType)
  deriving DecidableEq, Repr

def ResultType.expr : ResultType → Lean.Expr
  | .word => .const ``UInt64 []
  | .identity inner => .app (.const ``Id [.zero]) inner.expr

namespace Identity

/-- Canonical standard Id operations, including their complete instance evidence. -/
def run (body : Lean.Expr) (type : ResultType := .word) : Lean.Expr :=
  .app (.app (.const ``Id.run [.zero]) type.expr) body

def pure (body : Lean.Expr) (type : ResultType := .word) : Lean.Expr :=
  .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero])))) type.expr) body

def bind (name : Lean.Name) (bi : Lean.BinderInfo) (value body : Lean.Expr)
    (input output : ResultType := .word) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) input.expr) output.expr) value)
    (.lam name input.expr body bi)

end Identity
end LeanExe.Source.Scalar
