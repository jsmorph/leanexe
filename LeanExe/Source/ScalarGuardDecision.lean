import LeanExe.Source.ScalarGuard
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
      (leftMeaning : GuardDecision left leftEvidence)
      (rightMeaning : GuardDecision right rightEvidence) :
      GuardDecision (.junction negations operation left right)
        (GuardNegation.evidence negations (operation.condition left.condition right.condition)
          (operation.evidence left.condition right.condition leftEvidence rightEvidence))
  | boolean (propNegations boolNegations : Nat) (operation : Junction) (left right : BooleanGuard) :
      GuardDecision (.boolean propNegations boolNegations operation left right)
        (Guard.boolean propNegations boolNegations operation left right).evidence

theorem GuardDecision.canonical (guard : Guard) : GuardDecision guard guard.evidence := by
  induction guard with
  | literal value => exact .literal value
  | compare operation left right =>
    simpa [Guard.evidence] using GuardDecision.compare operation left right left right (.same left) (.same right)
  | junction n operation left right ihl ihr => exact .junction n operation left right ihl ihr
  | boolean m n operation left right => exact .boolean m n operation left right

/-- Noncanonical decision syntax for an independently supported guard tree. -/
structure ReannotatedGuard where
  tree : Guard
  evidence : Lean.Expr
  meaning : GuardDecision tree evidence
  different : evidence ≠ tree.evidence
  deriving Repr

abbrev ReannotatedGuard.condition (guard : ReannotatedGuard) := guard.tree.condition

end LeanExe.Source.Scalar
