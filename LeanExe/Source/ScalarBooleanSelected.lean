import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Source.Scalar

/-- A Boolean-valued choice with exact type and proof-binder annotations. -/
structure BooleanSelectionSyntax where
  type : BooleanType
  proof : Option BooleanProofBranch
  condition : Lean.Expr
  yes : Lean.Expr
  no : Lean.Expr

namespace BooleanSelectionSyntax

def proposition (value : BooleanSelectionSyntax) : Lean.Expr :=
  booleanRelationCondition false value.condition (booleanLiteralExpr true)

def evidence (value : BooleanSelectionSyntax) : Lean.Expr :=
  booleanRelationEvidence false value.condition (booleanLiteralExpr true)

def expr (value : BooleanSelectionSyntax) : Lean.Expr :=
  match value.proof with
  | none =>
    .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) value.type.expr)
      value.proposition) value.evidence) value.yes) value.no
  | some shape =>
    .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) value.type.expr)
      value.proposition) value.evidence)
      (.lam shape.trueName value.proposition (ExprProofBinder.lift 0 value.yes) shape.trueInfo))
      (.lam shape.falseName (.app (.const ``Not []) value.proposition)
        (ExprProofBinder.lift 0 value.no) shape.falseInfo)

theorem children_size (value : BooleanSelectionSyntax) :
    sizeOf value.condition < sizeOf value.expr ∧
      sizeOf value.yes < sizeOf value.expr ∧ sizeOf value.no < sizeOf value.expr := by
  rcases value with ⟨type, proof, condition, yes, no⟩
  have hy := ExprProofBinder.lift_size yes 0
  have hn := ExprProofBinder.lift_size no 0
  cases proof <;>
    simp [expr, proposition, evidence, booleanRelationCondition, booleanRelationEvidence,
      booleanLiteralExpr] <;> omega

end BooleanSelectionSyntax

/-- A Boolean choice outside the closed BooleanLocal grammar. -/
structure BooleanSelected where
  selection : BooleanSelectionSyntax
  extended : ∀ expression : BooleanLocal, selection.expr ≠ expression.expr

namespace BooleanSelected
abbrev expr (value : BooleanSelected) : Lean.Expr := value.selection.expr
end BooleanSelected
end LeanExe.Source.Scalar
