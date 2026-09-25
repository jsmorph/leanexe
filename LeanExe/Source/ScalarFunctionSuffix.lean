import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

/-- The two concrete binders of one UInt64 parameter retain their own names and
binder information in a function type and its lambda value. -/
structure Parameter where
  typeName : Lean.Name
  valueName : Lean.Name
  typeBi : Lean.BinderInfo
  valueBi : Lean.BinderInfo
  deriving Repr

def Parameter.arrow (parameter : Parameter) (rest : Lean.Expr) : Lean.Expr :=
  .forallE parameter.typeName (.const ``UInt64 []) rest parameter.typeBi

def Parameter.lambda (parameter : Parameter) (rest : Lean.Expr) : Lean.Expr :=
  .lam parameter.valueName (.const ``UInt64 []) rest parameter.valueBi

/-- A finite sequence of matching UInt64 parameters ending in a scalar result.
The original body remains available for the independent scalar source rules. -/
inductive FunctionSuffix where
  | result (annotation : ResultType) (body : Lean.Expr)
  | argument (parameter : Parameter) (rest : FunctionSuffix)
  deriving Repr

namespace FunctionSuffix

def type : FunctionSuffix → Lean.Expr
  | .result annotation _ => annotation.expr
  | .argument parameter rest => parameter.arrow rest.type

def value : FunctionSuffix → Lean.Expr
  | .result _ body => body
  | .argument parameter rest => parameter.lambda rest.value

def body : FunctionSuffix → Lean.Expr
  | .result _ body => body
  | .argument _ rest => rest.body

def arity : FunctionSuffix → Nat
  | .result .. => 0
  | .argument _ rest => rest.arity + 1

theorem body_size (suffix : FunctionSuffix) : sizeOf suffix.body ≤ sizeOf suffix.value := by
  induction suffix with
  | result => exact Nat.le_refl _
  | argument parameter rest ih =>
    simp only [body, value, Parameter.lambda]
    simp_all; omega

theorem body_size_strict (suffix : FunctionSuffix) (positive : 0 < suffix.arity) :
    sizeOf suffix.body < sizeOf suffix.value := by
  cases suffix with
  | result => simp [arity] at positive
  | argument parameter rest =>
    have bound := rest.body_size
    simp only [body, value, Parameter.lambda]
    simp_all; omega

end FunctionSuffix
end LeanExe.Source.Scalar
