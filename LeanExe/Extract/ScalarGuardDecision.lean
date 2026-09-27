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

def conditionChoice? (choices : List Lean.Expr) (condition : Lean.Expr) : Bool :=
  choices.any (LeanExe.Source.ExprEquality.same condition)

@[simp] theorem conditionChoice_eq_true (choices : List Lean.Expr) (condition : Lean.Expr) :
    conditionChoice? choices condition = true ↔ condition ∈ choices := by
  simp [conditionChoice?, List.any_eq_true]

/-- Check the connective, proposition arguments, child decisions and every negation wrapper. -/
def junctionEvidenceOperands? (n : Nat) (operation : Junction) (left right : Lean.Expr)
    (leftChoices rightChoices : List Lean.Expr) (evidence : Lean.Expr) :
    Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let inner ← stripDecisionNegations? n evidence
  match inner with
  | .app (.app (.app (.app _ leftProposition) rightProposition) leftEvidence) rightEvidence =>
      if conditionChoice? leftChoices leftProposition && conditionChoice? rightChoices rightProposition &&
          LeanExe.Source.ExprEquality.same evidence
            (GuardNegation.evidence n (operation.condition left right)
              (operation.evidence leftProposition rightProposition leftEvidence rightEvidence)) then
        some (leftProposition, rightProposition, leftEvidence, rightEvidence)
      else none
  | _ => none

@[simp] theorem junctionEvidenceOperands_accepts (n : Nat) (operation : Junction)
    (left right leftEvidence rightEvidence : Lean.Expr) (leftChoices rightChoices : List Lean.Expr)
    {leftProposition rightProposition : Lean.Expr}
    (leftMember : leftProposition ∈ leftChoices) (rightMember : rightProposition ∈ rightChoices) :
    junctionEvidenceOperands? n operation left right leftChoices rightChoices
      (GuardNegation.evidence n (operation.condition left right)
        (operation.evidence leftProposition rightProposition leftEvidence rightEvidence)) =
      some (leftProposition, rightProposition, leftEvidence, rightEvidence) := by
  simp [junctionEvidenceOperands?, stripDecisionNegations_accepts, Junction.evidence, leftMember, rightMember]

theorem junctionEvidenceOperands_sound {n : Nat} {operation : Junction}
    {left right evidence leftProposition rightProposition leftEvidence rightEvidence : Lean.Expr}
    {leftChoices rightChoices : List Lean.Expr}
    (found : junctionEvidenceOperands? n operation left right leftChoices rightChoices evidence =
      some (leftProposition, rightProposition, leftEvidence, rightEvidence)) :
    leftProposition ∈ leftChoices ∧ rightProposition ∈ rightChoices ∧
      evidence = GuardNegation.evidence n (operation.condition left right)
        (operation.evidence leftProposition rightProposition leftEvidence rightEvidence) := by
  simp only [junctionEvidenceOperands?, bind, Option.bind_eq_some_iff] at found
  obtain ⟨inner, _, accepted⟩ := found
  split at accepted
  · split at accepted
    · rename_i valid
      cases accepted
      simp only [Bool.and_eq_true, conditionChoice_eq_true, LeanExe.Source.ExprEquality.same_eq_true,
        and_assoc] at valid
      exact valid
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
      match junctionEvidenceOperands? n op left.condition right.condition left.conditionChoices right.conditionChoices evidence with
      | some (_, _, leftEvidence, rightEvidence) =>
          guardDecision? left leftEvidence && guardDecision? right rightEvidence
      | none => false
  | guard@(.boolean ..), evidence => LeanExe.Source.ExprEquality.same evidence guard.evidence

  | .savedLeft n op left right, evidence =>
      match junctionEvidenceOperands? n op left.condition right.condition [left.condition] right.conditionChoices evidence with
      | some (_, _, leftEvidence, rightEvidence) => LeanExe.Source.ExprEquality.same leftEvidence left.evidence && guardDecision? right rightEvidence
      | none => false
  | .savedRight n op left right, evidence =>
      match junctionEvidenceOperands? n op left.condition right.condition left.conditionChoices [right.condition] evidence with
      | some (_, _, leftEvidence, rightEvidence) => guardDecision? left leftEvidence && LeanExe.Source.ExprEquality.same rightEvidence right.evidence
      | none => false
  | guard@(.savedBoth ..), evidence => LeanExe.Source.ExprEquality.same evidence guard.evidence
  | guard@(.letGuard ..), evidence => LeanExe.Source.ExprEquality.same evidence guard.evidence
  | guard@(.letSaved ..), evidence => LeanExe.Source.ExprEquality.same evidence guard.evidence

@[simp] theorem guardDecision_accepts {guard : Guard} {evidence : Lean.Expr}
    (meaning : GuardDecision guard evidence) : guardDecision? guard evidence = true := by
  induction meaning with
  | literal value => simp [guardDecision?]
  | compare op left right decisionLeft decisionRight leftMeaning rightMeaning =>
    simp [guardDecision?, reannotation_accepts leftMeaning, reannotation_accepts rightMeaning]
  | junction n op left right leftCondition rightCondition leftMeaning rightMeaning ihl ihr =>
    simp [guardDecision?, leftCondition.mem_choices, rightCondition.mem_choices, ihl, ihr]
  | boolean => simp [guardDecision?]
  | savedLeft n op left right condition meaning ih => simp [guardDecision?, condition.mem_choices, ih]
  | savedRight n op left right condition meaning ih => simp [guardDecision?, condition.mem_choices, ih]
  | savedBoth => simp [guardDecision?, Guard.evidence]
  | letGuard => simp [guardDecision?]
  | letSaved => simp [guardDecision?]

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
    · rename_i leftProposition rightProposition leftEvidence rightEvidence found
      simp only [Bool.and_eq_true] at accepted
      obtain ⟨leftMember, rightMember, same⟩ := junctionEvidenceOperands_sound found
      rw [same]
      exact .junction n op left right (left.conditionChoices_sound leftMember)
        (right.conditionChoices_sound rightMember) (ihl accepted.1) (ihr accepted.2)
    · contradiction
  | boolean m n op left right =>
    have same := LeanExe.Source.ExprEquality.same_eq_true.mp accepted
    rw [same]
    exact .boolean m n op left right

  | savedLeft n op left right ih =>
    simp only [guardDecision?] at accepted
    split at accepted
    · rename_i leftProposition rightProposition leftEvidence rightEvidence found
      have same := accepted
      simp only [Bool.and_eq_true] at same
      obtain ⟨leftMember, rightMember, equal⟩ := junctionEvidenceOperands_sound found
      have leftSame : leftProposition = left.condition := List.mem_singleton.mp leftMember
      rw [equal, leftSame, LeanExe.Source.ExprEquality.same_eq_true.mp same.1]
      exact .savedLeft n op left right (right.conditionChoices_sound rightMember) (ih same.2)
    · contradiction
  | savedRight n op left right ih =>
    simp only [guardDecision?] at accepted
    split at accepted
    · rename_i leftProposition rightProposition leftEvidence rightEvidence found
      have same := accepted
      simp only [Bool.and_eq_true] at same
      obtain ⟨leftMember, rightMember, equal⟩ := junctionEvidenceOperands_sound found
      have rightSame : rightProposition = right.condition := List.mem_singleton.mp rightMember
      rw [equal, rightSame, LeanExe.Source.ExprEquality.same_eq_true.mp same.2]
      exact .savedRight n op left right (left.conditionChoices_sound leftMember) (ih same.1)
    · contradiction
  | savedBoth n op left right =>
    have same := LeanExe.Source.ExprEquality.same_eq_true.mp accepted
    rw [same]
    exact .savedBoth n op left right
  | letGuard n binding body _ =>
    have same := LeanExe.Source.ExprEquality.same_eq_true.mp accepted
    rw [same]
    exact .letGuard n binding body
  | letSaved n binding body =>
    have same := LeanExe.Source.ExprEquality.same_eq_true.mp accepted
    rw [same]
    exact .letSaved n binding body

@[simp] theorem guardDecision_canonical (guard : Guard) : guardDecision? guard guard.evidence = true :=
  guardDecision_accepts (.canonical guard)

end LeanExe.Extract.Core
