import LeanExe.Source.ScalarReannotatedComparison
import LeanExe.Extract.ScalarReannotation
import LeanExe.Extract.ScalarComparison

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

private def lastTwo? : Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | .app (.app _ left) right => some (left, right)
  | _ => none

/-- Locate candidate decision operands; the entire expression is checked below. -/
private def decisionOperands? : Comparison → Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | .ne _, .app _ inner => lastTwo? inner
  | .negate op, .app _ inner => decisionOperands? op inner
  | .beq, .app (.app _ inner) _ | .bne, .app (.app _ inner) _ => lastTwo? inner
  | .boolNot _, .app (.app _ (.app _ inner)) _ =>
      (booleanComparisonOperands? inner).map fun (_, a, b) => (a, b)
  | .gt _, expression | .ge _, expression => (lastTwo? expression).map Prod.swap
  | _, expression => lastTwo? expression

private theorem decisionOperands_accepts (op : Comparison) (a b da db : Lean.Expr) :
    decisionOperands? op (op.evidenceWith a b da db) = some (da, db) := by
  induction op with
  | negate op ih => simpa [Comparison.evidenceWith, decisionOperands?] using ih
  | boolNot op => simp [Comparison.evidenceWith, Comparison.evidence, decisionOperands?]
  | _ => rfl

def comparisonEvidenceOperands? (op : Comparison) (a b evidence : Lean.Expr) :
    Option (Lean.Expr × Lean.Expr) := do
  let (da, db) ← decisionOperands? op evidence
  if LeanExe.Source.ExprEquality.same evidence (op.evidenceWith a b da db) then some (da, db) else none

@[simp] theorem comparisonEvidenceOperands_accepts (op : Comparison) (a b da db : Lean.Expr) :
    comparisonEvidenceOperands? op a b (op.evidenceWith a b da db) = some (da, db) := by
  simp [comparisonEvidenceOperands?, decisionOperands_accepts]

theorem comparisonEvidenceOperands_sound {op : Comparison} {a b evidence da db : Lean.Expr}
    (found : comparisonEvidenceOperands? op a b evidence = some (da, db)) :
    evidence = op.evidenceWith a b da db := by
  simp only [comparisonEvidenceOperands?, bind, Option.bind_eq_some_iff] at found
  obtain ⟨⟨left, right⟩, _, accepted⟩ := found
  split at accepted
  · cases accepted
    exact LeanExe.Source.ExprEquality.same_eq_true.mp (by assumption)
  · contradiction

def reannotatedComparison? (condition evidence : Lean.Expr) : Option ReannotatedComparison := do
  let (op, a, b) ← comparisonOperands? condition
  let (da, db) ← comparisonEvidenceOperands? op a b evidence
  if left : reannotation? a da = true then
    if right : reannotation? b db = true then
      if different : op.evidenceWith a b da db ≠ op.evidence a b then
        some ⟨op, a, b, da, db, reannotation_sound left, reannotation_sound right, different⟩
      else none
    else none
  else none

@[simp] theorem reannotatedComparison_accepts (comparison : ReannotatedComparison) :
    reannotatedComparison? comparison.condition comparison.evidence = some comparison := by
  cases comparison with
  | mk op a b da db left right different =>
    simp [reannotatedComparison?, ReannotatedComparison.condition, ReannotatedComparison.evidence,
      reannotation_accepts left, reannotation_accepts right, different]

theorem reannotatedComparison_sound {condition evidence : Lean.Expr} {comparison : ReannotatedComparison}
    (found : reannotatedComparison? condition evidence = some comparison) :
    condition = comparison.condition ∧ evidence = comparison.evidence := by
  simp only [reannotatedComparison?, bind, Option.bind_eq_some_iff] at found
  obtain ⟨⟨op, a, b⟩, source, ⟨da, db⟩, decision, accepted⟩ := found
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted
        exact ⟨comparisonOperands_sound source, comparisonEvidenceOperands_sound decision⟩
      · contradiction
    · contradiction
  · contradiction

@[simp] theorem reannotatedComparison_not_comparison (comparison : ReannotatedComparison) :
    comparison? comparison.condition comparison.evidence = none := by
  have different := comparison.different
  simp [comparison?, ReannotatedComparison.condition, ReannotatedComparison.evidence, different]

end LeanExe.Extract.Core
