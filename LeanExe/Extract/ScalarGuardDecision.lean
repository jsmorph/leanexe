import LeanExe.Source.ScalarGuardDecision
import LeanExe.Extract.ScalarReannotatedComparison

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

private def stripDecisionNegations? : Nat → Lean.Expr → Option Lean.Expr
  | 0, evidence => some evidence
  | n + 1, .app _ evidence => stripDecisionNegations? n evidence
  | _, _ => none

private theorem stripDecisionNegations_accepts (n : Nat) (condition evidence : Lean.Expr) :
    stripDecisionNegations? n (GuardNegation.evidence n condition evidence) = some evidence := by
  induction n <;> simp_all [stripDecisionNegations?, GuardNegation.evidence]

/-- Find the two child decisions, then check all connective and proposition syntax. -/
def junctionEvidenceOperands? (n : Nat) (operation : Junction) (left right evidence : Lean.Expr) :
    Option (Lean.Expr × Lean.Expr) := do
  let inner ← stripDecisionNegations? n evidence
  match inner with
  | .app (.app _ leftEvidence) rightEvidence =>
      if LeanExe.Source.ExprEquality.same evidence
          (GuardNegation.evidence n (operation.condition left right)
            (operation.evidence left right leftEvidence rightEvidence)) then
        some (leftEvidence, rightEvidence)
      else none
  | _ => none

@[simp] theorem junctionEvidenceOperands_accepts (n : Nat) (operation : Junction)
    (left right leftEvidence rightEvidence : Lean.Expr) :
    junctionEvidenceOperands? n operation left right
      (GuardNegation.evidence n (operation.condition left right)
        (operation.evidence left right leftEvidence rightEvidence)) = some (leftEvidence, rightEvidence) := by
  simp [junctionEvidenceOperands?, stripDecisionNegations_accepts, Junction.evidence]

theorem junctionEvidenceOperands_sound {n : Nat} {operation : Junction}
    {left right evidence leftEvidence rightEvidence : Lean.Expr}
    (found : junctionEvidenceOperands? n operation left right evidence = some (leftEvidence, rightEvidence)) :
    evidence = GuardNegation.evidence n (operation.condition left right)
      (operation.evidence left right leftEvidence rightEvidence) := by
  simp only [junctionEvidenceOperands?, bind, Option.bind_eq_some_iff] at found
  obtain ⟨inner, _, accepted⟩ := found
  split at accepted
  · split at accepted
    · cases accepted
      exact LeanExe.Source.ExprEquality.same_eq_true.mp (by assumption)
    · contradiction
  · contradiction

def guardDecision? : Guard → Lean.Expr → Bool
  | .literal value, evidence => LeanExe.Source.ExprEquality.same evidence value.evidence
  | .compare op left right, evidence =>
      match comparisonEvidenceOperands? op left right evidence with
      | some (decisionLeft, decisionRight) =>
          reannotation? left decisionLeft && reannotation? right decisionRight
      | none => false
  | .junction n op left right, evidence =>
      match junctionEvidenceOperands? n op left.condition right.condition evidence with
      | some (leftEvidence, rightEvidence) =>
          guardDecision? left leftEvidence && guardDecision? right rightEvidence
      | none => false
  | guard@(.boolean ..), evidence => LeanExe.Source.ExprEquality.same evidence guard.evidence

@[simp] theorem guardDecision_accepts {guard : Guard} {evidence : Lean.Expr}
    (meaning : GuardDecision guard evidence) : guardDecision? guard evidence = true := by
  induction meaning with
  | literal value => simp [guardDecision?]
  | compare op left right decisionLeft decisionRight leftMeaning rightMeaning =>
    simp [guardDecision?, reannotation_accepts leftMeaning, reannotation_accepts rightMeaning]
  | junction n op left right leftMeaning rightMeaning ihl ihr => simp [guardDecision?, ihl, ihr]
  | boolean => simp [guardDecision?]

theorem guardDecision_sound {guard : Guard} {evidence : Lean.Expr}
    (accepted : guardDecision? guard evidence = true) : GuardDecision guard evidence := by
  induction guard generalizing evidence with
  | literal value =>
    have same := LeanExe.Source.ExprEquality.same_eq_true.mp accepted
    rw [same]
    exact .literal value
  | compare op left right =>
    simp only [guardDecision?] at accepted
    split at accepted
    · rename_i decisionLeft decisionRight found
      simp only [Bool.and_eq_true] at accepted
      rw [comparisonEvidenceOperands_sound found]
      exact .compare op left right decisionLeft decisionRight
        (reannotation_sound accepted.1) (reannotation_sound accepted.2)
    · contradiction
  | junction n op left right ihl ihr =>
    simp only [guardDecision?] at accepted
    split at accepted
    · rename_i leftEvidence rightEvidence found
      simp only [Bool.and_eq_true] at accepted
      rw [junctionEvidenceOperands_sound found]
      exact .junction n op left right (ihl accepted.1) (ihr accepted.2)
    · contradiction
  | boolean m n op left right =>
    have same := LeanExe.Source.ExprEquality.same_eq_true.mp accepted
    rw [same]
    exact .boolean m n op left right

@[simp] theorem guardDecision_canonical (guard : Guard) : guardDecision? guard guard.evidence = true :=
  guardDecision_accepts (.canonical guard)

end LeanExe.Extract.Core
