import LeanExe.Source.ScalarBooleanEqualityForm

namespace LeanExe.Source.Scalar

/-- Exact standard Boolean comparison relation with unparsed operands. -/
structure BooleanRelationSyntax where
  form : BooleanEqualityForm
  unequal : Bool
  left : Lean.Expr
  right : Lean.Expr

namespace BooleanRelationSyntax

def expr (value : BooleanRelationSyntax) : Lean.Expr :=
  match value.form with
  | .equality => booleanEqualityExpr value.unequal value.left value.right
  | .decision => booleanRelationDecisionExpr value.unequal value.left value.right

def denote (value : BooleanRelationSyntax) (a b : Bool) : Bool :=
  value.form.denote value.unequal a b

theorem children_size (value : BooleanRelationSyntax) :
    sizeOf value.left < sizeOf value.expr ∧ sizeOf value.right < sizeOf value.expr := by
  rcases value with ⟨form, unequal, left, right⟩
  cases form <;> cases unequal <;>
    simp [expr, booleanEqualityExpr, booleanRelationDecisionExpr,
      booleanRelationCondition, booleanRelationEvidence] <;> omega

end BooleanRelationSyntax

/-- A Boolean relation outside the closed BooleanLocal grammar. -/
structure BooleanRelated where
  relation : BooleanRelationSyntax
  extended : ∀ expression : BooleanLocal, relation.expr ≠ expression.expr

namespace BooleanRelated
abbrev expr (value : BooleanRelated) : Lean.Expr := value.relation.expr
end BooleanRelated
end LeanExe.Source.Scalar
