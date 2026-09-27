import LeanExe.Source.ScalarBooleanCall

namespace LeanExe.Source.Scalar

/-- Preserve a local function declaration while selecting its enclosing body. -/
def BooleanFunctionBinding.bodyExpr (shape : BooleanFunctionBinding)
    (parameterName : Lean.Name) (input value body : Lean.Expr) : Lean.Expr :=
  .letE shape.functionName
    (.forallE shape.typeName input shape.result.expr shape.typeInfo)
    (.lam parameterName input value shape.valueInfo) body shape.nondep

/-- The condition is outside the helper binding; both arms retain that binding. -/
structure BooleanFunctionChoice where
  output : BooleanType
  condition : Lean.Expr
  evidence : Lean.Expr
  yes : Lean.Expr
  no : Lean.Expr
  deriving Repr

def BooleanFunctionChoice.expr (choice : BooleanFunctionChoice) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) choice.output.expr)
    (LeanExe.Source.ExprProofBinder.lift 0 choice.condition))
    (LeanExe.Source.ExprProofBinder.lift 0 choice.evidence)) choice.yes) choice.no

theorem BooleanFunctionChoice.arm_sizes (choice : BooleanFunctionChoice) :
    sizeOf choice.yes < sizeOf choice.expr ∧ sizeOf choice.no < sizeOf choice.expr := by
  simp only [BooleanFunctionChoice.expr]
  simp
  omega

end LeanExe.Source.Scalar
