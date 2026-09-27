import LeanExe.Source.ScalarSavedBooleanGuard
import LeanExe.Extract.ScalarBooleanGuardSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def savedBooleanValue? : Lean.Expr → Option (Nat × Nat)
  | .bvar index => some (index, 0)
  | .app (.const ``Bool.not []) value => do
      let (index, negations) ← savedBooleanValue? value
      some (index, negations + 1)
  | _ => none

@[simp] theorem savedBooleanValue_accepts (index negations : Nat) :
    savedBooleanValue? (BooleanGuardNegation.expr negations (.bvar index)) = some (index, negations) := by
  induction negations <;> simp_all [BooleanGuardNegation.expr, savedBooleanValue?]

theorem savedBooleanValue_sound {value : Lean.Expr} {index negations : Nat}
    (parsed : savedBooleanValue? value = some (index, negations)) :
    value = BooleanGuardNegation.expr negations (.bvar index) := by
  induction value using savedBooleanValue?.induct generalizing index negations with
  | case1 idx => cases parsed; rfl
  | case2 value ih =>
    simp only [savedBooleanValue?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨⟨idx, n⟩, found, same⟩ := parsed
    cases same
    simp [BooleanGuardNegation.expr, ih found]
  | case3 value noVar noNot =>
    rw [savedBooleanValue?] at parsed
    · cases parsed
    · exact noVar
    · exact noNot

def savedBooleanGuard? : Lean.Expr → Option SavedBooleanGuard
  | .app (.const ``Not []) value => (savedBooleanGuard? value).map SavedBooleanGuard.negate
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value) (.const ``Bool.true []) => do
      let (index, negations) ← savedBooleanValue? value
      some ⟨index, negations, 0⟩
  | _ => none

@[simp] theorem savedBooleanGuard_accepts (guard : SavedBooleanGuard) :
    savedBooleanGuard? guard.condition = some guard := by
  obtain ⟨index, negations, propNegations⟩ := guard
  induction propNegations with
  | zero => simp [SavedBooleanGuard.condition, SavedBooleanGuard.expr, GuardNegation.condition, savedBooleanGuard?]
  | succ n ih =>
    simpa only [SavedBooleanGuard.condition, GuardNegation.condition, savedBooleanGuard?,
      Option.map_some, SavedBooleanGuard.negate, SavedBooleanGuard.expr] using congrArg (Option.map SavedBooleanGuard.negate) ih

theorem savedBooleanGuard_sound {condition : Lean.Expr} {guard : SavedBooleanGuard}
    (parsed : savedBooleanGuard? condition = some guard) : condition = guard.condition := by
  induction condition using savedBooleanGuard?.induct generalizing guard with
  | case1 value ih =>
    rw [savedBooleanGuard?] at parsed
    obtain ⟨inner, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rw [SavedBooleanGuard.negate_condition, ih found]
  | case2 value =>
    simp only [savedBooleanGuard?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨⟨index, negations⟩, found, rfl⟩ := parsed
    simp [SavedBooleanGuard.condition, SavedBooleanGuard.expr, GuardNegation.condition,
      savedBooleanValue_sound found]
  | case3 value noNot noTruth =>
    rw [savedBooleanGuard?] at parsed
    · cases parsed
    · exact noNot
    · exact noTruth

theorem savedBooleanValue_not_comparison (index negations : Nat) :
    booleanComparisonOperands? (BooleanGuardNegation.expr negations (.bvar index)) = none := by
  induction negations <;> simp_all [BooleanGuardNegation.expr, booleanComparisonOperands?]

theorem savedBooleanValue_not_closed (index negations : Nat) :
    booleanGuardOperands? (BooleanGuardNegation.expr negations (.bvar index)) = none := by
  induction negations <;> simp_all [BooleanGuardNegation.expr, booleanGuardOperands?, booleanComparisonOperands?]

end LeanExe.Extract.Core
