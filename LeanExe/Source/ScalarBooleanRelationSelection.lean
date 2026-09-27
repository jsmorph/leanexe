import LeanExe.Source.ScalarBooleanSelected

namespace LeanExe.Source.Scalar

/-- Exact Boolean Eq/Ne syntax, excluding the separate Boolean-truth path. -/
structure BooleanRelationGuard where
  unequal : Bool
  left : Lean.Expr
  right : Lean.Expr
  nontruth : unequal = false → right ≠ .const ``Bool.true []

namespace BooleanRelationGuard

def leaf (guard : BooleanRelationGuard) : BooleanPropositionLeaf :=
  .relation guard.unequal guard.left guard.right guard.nontruth

def condition (guard : BooleanRelationGuard) : Lean.Expr := guard.leaf.condition

def evidence (guard : BooleanRelationGuard) : Lean.Expr := guard.leaf.evidence

def denote (guard : BooleanRelationGuard) (a b : Bool) : Bool :=
  booleanRelationDecision guard.unequal a b

theorem not_boolean_condition (guard : BooleanRelationGuard) (operand : Lean.Expr) :
    guard.condition ≠ booleanRelationCondition false operand (booleanLiteralExpr true) := by
  rcases guard with ⟨unequal, left, right, nontruth⟩
  cases unequal with
  | false => simp [condition, leaf, BooleanPropositionLeaf.condition,
      booleanRelationCondition, booleanLiteralExpr, nontruth rfl]
  | true => simp [condition, leaf, BooleanPropositionLeaf.condition,
      booleanRelationCondition, booleanLiteralExpr]

end BooleanRelationGuard

/-- A Boolean-valued choice over a native Boolean Eq/Ne condition. -/
structure BooleanRelationSelectionSyntax where
  type : BooleanType
  proof : Option BooleanProofBranch
  guard : BooleanRelationGuard
  yes : Lean.Expr
  no : Lean.Expr

namespace BooleanRelationSelectionSyntax

def expr (value : BooleanRelationSelectionSyntax) : Lean.Expr :=
  match value.proof with
  | none =>
    .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) value.type.expr)
      value.guard.condition) value.guard.evidence) value.yes) value.no
  | some shape =>
    .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) value.type.expr)
      value.guard.condition) value.guard.evidence)
      (.lam shape.trueName value.guard.condition (ExprProofBinder.lift 0 value.yes) shape.trueInfo))
      (.lam shape.falseName (.app (.const ``Not []) value.guard.condition)
        (ExprProofBinder.lift 0 value.no) shape.falseInfo)

theorem children_size (value : BooleanRelationSelectionSyntax) :
    sizeOf value.guard.left < sizeOf value.expr ∧ sizeOf value.guard.right < sizeOf value.expr ∧
      sizeOf value.yes < sizeOf value.expr ∧ sizeOf value.no < sizeOf value.expr := by
  rcases value with ⟨type, proof, ⟨unequal, left, right, nontruth⟩, yes, no⟩
  have hy := ExprProofBinder.lift_size yes 0
  have hn := ExprProofBinder.lift_size no 0
  cases proof <;> cases unequal <;>
    simp [expr, BooleanRelationGuard.condition, BooleanRelationGuard.leaf,
      BooleanPropositionLeaf.condition] <;> omega

end BooleanRelationSelectionSyntax

/-- A Boolean relation choice outside the closed BooleanLocal grammar. -/
structure BooleanRelationSelection where
  selection : BooleanRelationSelectionSyntax
  extended : ∀ expression : BooleanLocal, selection.expr ≠ expression.expr

namespace BooleanRelationSelection
abbrev expr (value : BooleanRelationSelection) : Lean.Expr := value.selection.expr
end BooleanRelationSelection
end LeanExe.Source.Scalar
