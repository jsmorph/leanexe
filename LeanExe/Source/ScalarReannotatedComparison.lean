import LeanExe.Source.ScalarComparison
import LeanExe.Source.ScalarReannotation

namespace LeanExe.Source.Scalar

/-- Standard comparison evidence with separately elaborated arithmetic operands.
Propositions appearing in negation evidence retain the original condition operands. -/
def Comparison.evidenceWith : Comparison → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr
  | .ne type, a, b, da, db =>
      .app (.app (.const ``instDecidableNot []) (Comparison.condition (.eq type) a b))
        (Comparison.evidence (.eq type) da db)
  | .negate op, a, b, da, db =>
      .app (.app (.const ``instDecidableNot []) (op.condition a b)) (op.evidenceWith a b da db)
  | op, _, _, da, db => op.evidence da db

@[simp] theorem Comparison.evidenceWith_same (op : Comparison) (a b : Lean.Expr) :
    op.evidenceWith a b a b = op.evidence a b := by
  induction op <;> simp_all [Comparison.evidenceWith, Comparison.evidence]

/-- A comparison whose decision operands have the same source evaluations as
its condition operands. Exact canonical evidence uses the ordinary comparison form. -/
structure ReannotatedComparison where
  operation : Comparison
  left : Lean.Expr
  right : Lean.Expr
  decisionLeft : Lean.Expr
  decisionRight : Lean.Expr
  leftMeaning : Reannotates left decisionLeft
  rightMeaning : Reannotates right decisionRight
  different : operation.evidenceWith left right decisionLeft decisionRight ≠ operation.evidence left right
  deriving Repr

namespace ReannotatedComparison

abbrev condition (comparison : ReannotatedComparison) :=
  comparison.operation.condition comparison.left comparison.right
abbrev evidence (comparison : ReannotatedComparison) :=
  comparison.operation.evidenceWith comparison.left comparison.right comparison.decisionLeft comparison.decisionRight

end ReannotatedComparison
end LeanExe.Source.Scalar
