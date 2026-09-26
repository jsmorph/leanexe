import LeanExe.Source.ScalarBooleanType

namespace LeanExe.Source.Scalar

namespace BooleanIdentity

def run (body : Lean.Expr) (type : BooleanType := .boolean) : Lean.Expr :=
  .app (.app (.const ``Id.run [.zero]) type.expr) body

def pure (body : Lean.Expr) (type : BooleanType := .boolean) : Lean.Expr :=
  .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
        (.const ``Id.instMonad [.zero])))) type.expr) body

def bind (name : Lean.Name) (bi : Lean.BinderInfo) (value body result : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) (.const ``Bool [])) result) value)
    (.lam name (.const ``Bool []) body bi)

end BooleanIdentity

/-- Exact standard Id syntax and metadata around a Boolean value. -/
inductive BooleanWrapper where
  | run (type : BooleanType := .boolean)
  | pure (type : BooleanType := .boolean)
  | metadata (data : Lean.MData)
  deriving Repr

namespace BooleanWrapper

def expr : BooleanWrapper → Lean.Expr → Lean.Expr
  | .run type, body => BooleanIdentity.run body type
  | .pure type, body => BooleanIdentity.pure body type
  | .metadata data, body => .mdata data body

def denote : BooleanWrapper → Bool → Bool
  | .run _, value => Id.run value
  | .pure _, value => (Pure.pure value : Id Bool)
  | .metadata _, value => value

@[simp] theorem denote_eq (wrapper : BooleanWrapper) (value : Bool) :
    wrapper.denote value = value := by cases wrapper <;> rfl

theorem body_size (wrapper : BooleanWrapper) (body : Lean.Expr) :
    sizeOf body < sizeOf (wrapper.expr body) := by
  cases wrapper <;> simp [expr, BooleanIdentity.run, BooleanIdentity.pure] <;> omega

end BooleanWrapper
end LeanExe.Source.Scalar
