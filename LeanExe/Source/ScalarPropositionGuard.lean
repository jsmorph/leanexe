import LeanExe.Source.ScalarDecidedGuard

namespace LeanExe.Source.Scalar

/-- Direct Boolean coercions retain the separate Boolean-expression path. -/
def Guard.hasBooleanCondition : Guard → Bool
  | .literal (.boolean 0 _ _) => true
  | .compare .beq _ _ | .compare .bne _ _ | .compare (.boolNot _) _ _ => true
  | .boolean 0 _ _ _ _ => true
  | _ => false

/-- A closed guard whose outer condition is propositional syntax. -/
structure PropositionGuard where
  value : DecidedGuard
  nonboolean : value.tree.hasBooleanCondition = false
  deriving Repr

namespace PropositionGuard

abbrev condition (guard : PropositionGuard) := guard.value.condition
abbrev evidence (guard : PropositionGuard) := guard.value.evidence
abbrev operands (guard : PropositionGuard) := guard.value.operands
abbrev denote (guard : PropositionGuard) (native : Lean.Expr → UInt64) := guard.value.denote native

theorem not_boolean_condition (guard : PropositionGuard) (expression : Lean.Expr) :
    guard.condition ≠ .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) expression)
      (.const ``Bool.true []) := by
  rcases guard with ⟨⟨value, evidence, meaning⟩, nonboolean⟩
  cases value with
  | literal value =>
    cases value with
    | proposition n value =>
      cases n with
      | zero => cases value <;> simp [condition, DecidedGuard.condition, Guard.condition, GuardLiteral.condition,
          GuardNegation.condition, GuardLiteral.propositionExpr]
      | succ n => simp [condition, DecidedGuard.condition, Guard.condition, GuardLiteral.condition, GuardNegation.condition]
    | boolean m n value =>
      cases m with
      | zero => simp [Guard.hasBooleanCondition] at nonboolean
      | succ m => simp [condition, DecidedGuard.condition, Guard.condition, GuardLiteral.condition, GuardNegation.condition]
  | compare op a b =>
    cases op <;> simp [Guard.hasBooleanCondition] at nonboolean
    all_goals simp [condition, DecidedGuard.condition, Guard.condition, Comparison.condition]
  | junction n op a b =>
    cases n with
    | zero => cases op <;> simp [condition, DecidedGuard.condition, Guard.condition, GuardNegation.condition, Junction.condition]
    | succ n => simp [condition, DecidedGuard.condition, Guard.condition, GuardNegation.condition]
  | boolean m n op a b =>
    cases m with
    | zero => simp [Guard.hasBooleanCondition] at nonboolean
    | succ m => simp [condition, DecidedGuard.condition, Guard.condition, GuardNegation.condition]

def branch (guard : PropositionGuard) (yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Bool []))
    guard.condition) guard.evidence) yes) no

end PropositionGuard
end LeanExe.Source.Scalar
