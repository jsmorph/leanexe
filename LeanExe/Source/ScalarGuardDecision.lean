import LeanExe.Source.ScalarGuardCondition
import LeanExe.Source.ScalarReannotatedComparison

namespace LeanExe.Source.Scalar

/-- Standard decision syntax for a guard. Arithmetic leaves may use separately
elaborated operands whose source evaluations are proved equivalent. -/
inductive GuardDecision : Guard → Lean.Expr → Prop where
  | literal (value : GuardLiteral) : GuardDecision (.literal value) value.evidence
  | compare (operation : Comparison) (left right decisionLeft decisionRight : Lean.Expr)
      (leftMeaning : Reannotates left decisionLeft)
      (rightMeaning : Reannotates right decisionRight) :
      GuardDecision (.compare operation left right)
        (operation.evidenceWith left right decisionLeft decisionRight)
  | junction (negations : Nat) (operation : Junction) (left right : Guard)
      (leftCondition : GuardCondition left leftProposition)
      (rightCondition : GuardCondition right rightProposition)
      (leftMeaning : GuardDecision left leftEvidence)
      (rightMeaning : GuardDecision right rightEvidence) :
      GuardDecision (.junction negations operation left right)
        (GuardNegation.evidence negations (operation.condition left.condition right.condition)
          (operation.evidence leftProposition rightProposition leftEvidence rightEvidence))
  | boolean (propNegations boolNegations : Nat) (operation : Junction) (left right : BooleanGuard) :
      GuardDecision (.boolean propNegations boolNegations operation left right)
        (Guard.boolean propNegations boolNegations operation left right).evidence
  | savedLeft (negations : Nat) (operation : Junction) (left : SavedBooleanGuard) (right : Guard)
      (rightCondition : GuardCondition right rightProposition)
      (rightMeaning : GuardDecision right rightEvidence) :
      GuardDecision (.savedLeft negations operation left right)
        (GuardNegation.evidence negations (operation.condition left.condition right.condition)
          (operation.evidence left.condition rightProposition left.evidence rightEvidence))
  | savedRight (negations : Nat) (operation : Junction) (left : Guard) (right : SavedBooleanGuard)
      (leftCondition : GuardCondition left leftProposition)
      (leftMeaning : GuardDecision left leftEvidence) :
      GuardDecision (.savedRight negations operation left right)
        (GuardNegation.evidence negations (operation.condition left.condition right.condition)
          (operation.evidence leftProposition right.condition leftEvidence right.evidence))
  | savedBoth (negations : Nat) (operation : Junction) (left right : SavedBooleanGuard) :
      GuardDecision (.savedBoth negations operation left right)
        (GuardNegation.evidence negations (operation.condition left.condition right.condition)
          (operation.evidence left.condition right.condition left.evidence right.evidence))

  | letGuard (negations : Nat) (binding : GuardLet) (body : Guard) :
      GuardDecision (.letGuard negations binding body) (Guard.letGuard negations binding body).evidence
  | letSaved (negations : Nat) (binding : GuardLet) (body : SavedBooleanGuard) :
      GuardDecision (.letSaved negations binding body) (Guard.letSaved negations binding body).evidence

theorem GuardDecision.canonical (guard : Guard) : GuardDecision guard guard.evidence := by
  induction guard with
  | literal value => exact .literal value
  | compare operation left right =>
    simpa [Guard.evidence] using GuardDecision.compare operation left right left right (.same left) (.same right)
  | junction n operation left right ihl ihr => exact .junction n operation left right (.retained left) (.retained right) ihl ihr
  | boolean m n operation left right => exact .boolean m n operation left right
  | savedLeft n op left right ih => exact .savedLeft n op left right (.retained right) ih
  | savedRight n op left right ih => exact .savedRight n op left right (.retained left) ih
  | savedBoth n op left right => exact .savedBoth n op left right
  | letGuard n binding body _ => exact .letGuard n binding body
  | letSaved n binding body => exact .letSaved n binding body

/-- Noncanonical decision syntax for an independently supported guard tree. -/
structure ReannotatedGuard where
  tree : Guard
  evidence : Lean.Expr
  meaning : GuardDecision tree evidence
  different : evidence ≠ tree.evidence
  deriving Repr

abbrev ReannotatedGuard.condition (guard : ReannotatedGuard) := guard.tree.condition

end LeanExe.Source.Scalar
