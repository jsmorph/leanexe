import LeanExe.Source.ScalarBooleanLocal
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

/-- Pure Boolean actions retain standard Id wrappers without changing the leaf's
value, captured Boolean variables or scalar comparison operands. -/
inductive BooleanAction where
  | value (expression : BooleanLocal)
  | pure (body : BooleanAction) (type : BooleanType := .boolean)
  | run (body : BooleanAction) (type : BooleanType := .boolean)
  | metadata (data : Lean.MData) (body : BooleanAction)

namespace BooleanAction

def leaf : BooleanAction → BooleanLocal
  | .value expression => expression
  | .pure body _ | .run body _ | .metadata _ body => body.leaf

def expr : BooleanAction → Lean.Expr
  | .value expression => expression.expr
  | .pure body type => BooleanIdentity.pure body.expr type
  | .run body type => BooleanIdentity.run body.expr type
  | .metadata data body => .mdata data body.expr

theorem operands_size (action : BooleanAction) {operand : Lean.Expr}
    (member : operand ∈ action.leaf.operands) : sizeOf operand < sizeOf action.expr := by
  induction action with
  | value expression => exact expression.operands_size member
  | pure body type ih => have h := ih member; simp_all [leaf, expr, BooleanIdentity.pure]; omega
  | run body type ih => have h := ih member; simp_all [leaf, expr, BooleanIdentity.run]; omega
  | metadata data body ih => have h := ih member; simp_all [leaf, expr]; omega

end BooleanAction
end LeanExe.Source.Scalar
