import LeanExe.Source.ScalarBooleanCall

namespace LeanExe.Source.Scalar

/-- Preserve a local function declaration while selecting its enclosing body. -/
def BooleanFunctionBinding.bodyExpr (shape : BooleanFunctionBinding)
    (parameterName : Lean.Name) (input value body : Lean.Expr) : Lean.Expr :=
  .letE shape.functionName
    (.forallE shape.typeName input shape.result.expr shape.typeInfo)
    (.lam parameterName input value shape.valueInfo) body shape.nondep

/-- Conditional helper calls retain standard wrappers and saved Boolean results. -/
inductive BooleanFunctionChoice where
  | mk (output : BooleanType) (condition evidence yes no : Lean.Expr)
  | wrapped (wrapper : BooleanWrapper) (inner : BooleanFunctionChoice)
  | savedResult (name : Lean.Name) (type : BooleanType) (nondep : Bool)
      (inner : BooleanFunctionChoice)
  deriving Repr

def BooleanFunctionChoice.output : BooleanFunctionChoice → BooleanType
  | .mk output _ _ _ _ => output
  | .wrapped _ inner | .savedResult _ _ _ inner => inner.output

def BooleanFunctionChoice.condition : BooleanFunctionChoice → Lean.Expr
  | .mk _ condition _ _ _ => condition
  | .wrapped _ inner | .savedResult _ _ _ inner => inner.condition

def BooleanFunctionChoice.evidence : BooleanFunctionChoice → Lean.Expr
  | .mk _ _ evidence _ _ => evidence
  | .wrapped _ inner | .savedResult _ _ _ inner => inner.evidence

def BooleanFunctionChoice.yes : BooleanFunctionChoice → Lean.Expr
  | .mk _ _ _ yes _ => yes
  | .wrapped _ inner | .savedResult _ _ _ inner => inner.yes

def BooleanFunctionChoice.no : BooleanFunctionChoice → Lean.Expr
  | .mk _ _ _ _ no => no
  | .wrapped _ inner | .savedResult _ _ _ inner => inner.no

def BooleanFunctionChoice.expr : BooleanFunctionChoice → Lean.Expr
  | .mk output condition evidence yes no =>
      .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) output.expr)
        (LeanExe.Source.ExprProofBinder.lift 0 condition))
        (LeanExe.Source.ExprProofBinder.lift 0 evidence)) yes) no
  | .wrapped wrapper inner => wrapper.expr inner.expr
  | .savedResult name type nondep inner => .letE name type.expr inner.expr (.bvar 0) nondep

theorem BooleanFunctionChoice.arm_sizes (choice : BooleanFunctionChoice) :
    sizeOf choice.yes < sizeOf choice.expr ∧ sizeOf choice.no < sizeOf choice.expr := by
  induction choice with
  | mk output condition evidence yes no =>
    simp only [BooleanFunctionChoice.expr, BooleanFunctionChoice.yes, BooleanFunctionChoice.no]
    simp
    omega
  | wrapped wrapper inner ih =>
    exact ⟨Nat.lt_trans ih.1 (wrapper.body_size inner.expr), Nat.lt_trans ih.2 (wrapper.body_size inner.expr)⟩
  | savedResult name type nondep inner ih =>
    have smaller : sizeOf inner.expr < sizeOf (Lean.Expr.letE name type.expr inner.expr (.bvar 0) nondep) := by simp; omega
    exact ⟨Nat.lt_trans ih.1 smaller, Nat.lt_trans ih.2 smaller⟩

end LeanExe.Source.Scalar
