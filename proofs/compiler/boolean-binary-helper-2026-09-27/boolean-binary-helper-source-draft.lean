import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Source.ScalarFunctionSuffix

namespace LeanExe.Source.Scalar

/-- Both type and value binders of a local two-word predicate are retained. -/
structure BooleanBinaryFunctionBinding where
  name : Lean.Name
  first : Parameter
  second : Parameter
  result : BooleanType
  nondep : Bool
  deriving Repr

namespace BooleanBinaryFunctionBinding

def expr (shape : BooleanBinaryFunctionBinding) (body continuation : Lean.Expr) : Lean.Expr :=
  .letE shape.name (shape.first.arrow (shape.second.arrow shape.result.expr))
    (shape.first.lambda (shape.second.lambda body)) continuation shape.nondep

/-- A checked binary predicate body is evaluated with arguments in source order. -/
theorem apply (body : UInt64 → UInt64 → Bool) (first second : UInt64) :
    (fun x y => body x y) first second = body first second := rfl

end BooleanBinaryFunctionBinding

/-- Exact predicate declaration with an independently checked continuation. -/
structure BooleanBinaryHelper where
  shape : BooleanBinaryFunctionBinding
  body : Lean.Expr
  continuation : Lean.Expr
  extended : ∀ expression : BooleanLocal,
    shape.expr body continuation ≠ expression.expr
  deriving Repr

namespace BooleanBinaryHelper

def expr (helper : BooleanBinaryHelper) : Lean.Expr := helper.shape.expr helper.body helper.continuation

theorem body_size (helper : BooleanBinaryHelper) : sizeOf helper.body < sizeOf helper.expr := by
  simp [expr, BooleanBinaryFunctionBinding.expr, Parameter.arrow, Parameter.lambda]; omega

theorem continuation_size (helper : BooleanBinaryHelper) : sizeOf helper.continuation < sizeOf helper.expr := by
  simp [expr, BooleanBinaryFunctionBinding.expr, Parameter.arrow, Parameter.lambda]; omega

end BooleanBinaryHelper

/-- A binary predicate call supplies both arguments to one lexical function. -/
structure BooleanBinaryCall where
  index : Nat
  first : Lean.Expr
  second : Lean.Expr
  deriving Repr

namespace BooleanBinaryCall

def expr (call : BooleanBinaryCall) : Lean.Expr := .app (.app (.bvar call.index) call.first) call.second

theorem first_size (call : BooleanBinaryCall) : sizeOf call.first < sizeOf call.expr := by
  simp [expr]; omega

theorem second_size (call : BooleanBinaryCall) : sizeOf call.second < sizeOf call.expr := by
  simp [expr]; omega

end BooleanBinaryCall
end LeanExe.Source.Scalar
