import LeanExe.Source.ScalarFunctionSuffix

namespace LeanExe.Source.Scalar

/-- A larger local scalar helper extends the two existing UInt64 parameters by
one or more further checked parameters. All arities share this description. -/
structure ManyFunction where
  first : Parameter
  second : Parameter
  suffix : FunctionSuffix
  positive : 0 < suffix.arity

namespace ManyFunction

def type (function : ManyFunction) (render : ResultType → Lean.Expr := ResultType.expr) : Lean.Expr :=
  function.first.arrow (function.second.arrow (function.suffix.type render))

def value (function : ManyFunction) : Lean.Expr :=
  function.first.lambda (function.second.lambda function.suffix.value)

abbrev body (function : ManyFunction) : Lean.Expr := function.suffix.body
abbrev arity (function : ManyFunction) : Nat := function.suffix.arity + 2

theorem arity_ge_three (function : ManyFunction) : 3 ≤ function.arity := by
  have positive := function.positive
  simp only [arity]
  omega

theorem body_size (function : ManyFunction) : sizeOf function.body < sizeOf function.value := by
  have bound := function.suffix.body_size
  simp only [body, value, Parameter.lambda]
  simp_all; omega

def bind (function : ManyFunction) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool)
    (render : ResultType → Lean.Expr := ResultType.expr) : Lean.Expr :=
  .letE name (function.type render) function.value body nondep

theorem body_bind_size (function : ManyFunction) (name : Lean.Name) (body : Lean.Expr) (nondep : Bool) :
    sizeOf function.body < sizeOf (function.bind name body nondep) := by
  have bound := function.body_size
  simp only [bind]
  simp_all; omega

end ManyFunction
end LeanExe.Source.Scalar
