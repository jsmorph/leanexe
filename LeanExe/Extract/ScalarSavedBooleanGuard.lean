import LeanExe.Source.ScalarSavedBooleanGuard
import LeanExe.Extract.ScalarBooleanGuardSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def savedBooleanValue? : Lean.Expr → Option (Nat × Nat × Option Lean.Expr)
  | .bvar index => some (index, 0, none)
  | .app (.bvar index) argument => some (index, 0, some argument)
  | .app (.const ``Bool.not []) value => do
      let (index, negations, argument) ← savedBooleanValue? value
      some (index, negations + 1, argument)
  | _ => none

@[simp] theorem savedBooleanValue_accepts (index negations : Nat) (argument : Option Lean.Expr) :
    savedBooleanValue? (BooleanGuardNegation.expr negations (SavedBooleanGuard.reference index argument)) =
      some (index, negations, argument) := by
  induction negations with
  | zero => cases argument <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, savedBooleanValue?, ih]

theorem savedBooleanValue_sound {value : Lean.Expr} {index negations : Nat} {argument : Option Lean.Expr}
    (parsed : savedBooleanValue? value = some (index, negations, argument)) :
    value = BooleanGuardNegation.expr negations (SavedBooleanGuard.reference index argument) := by
  induction value using savedBooleanValue?.induct generalizing index negations argument with
  | case1 idx => cases parsed; rfl
  | case2 idx arg => cases parsed; rfl
  | case3 value ih =>
    simp only [savedBooleanValue?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨⟨idx, n, arg⟩, found, same⟩ := parsed
    cases same
    simp [BooleanGuardNegation.expr, ih found]
  | case4 value noVar noCall noNot =>
    rw [savedBooleanValue?] at parsed
    · cases parsed
    · exact noVar
    · exact noCall
    · exact noNot

def savedBooleanGuard? : Lean.Expr → Option SavedBooleanGuard
  | .app (.const ``Not []) value => (savedBooleanGuard? value).map SavedBooleanGuard.negate
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value) (.const ``Bool.true []) => do
      let (index, negations, argument) ← savedBooleanValue? value
      some ⟨index, negations, 0, argument⟩
  | _ => none

@[simp] theorem savedBooleanGuard_accepts (guard : SavedBooleanGuard) :
    savedBooleanGuard? guard.condition = some guard := by
  obtain ⟨index, negations, propNegations, argument⟩ := guard
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
    obtain ⟨⟨index, negations, argument⟩, found, rfl⟩ := parsed
    simp [SavedBooleanGuard.condition, SavedBooleanGuard.expr, GuardNegation.condition,
      savedBooleanValue_sound found]
  | case3 value noNot noTruth =>
    rw [savedBooleanGuard?] at parsed
    · cases parsed
    · exact noNot
    · exact noTruth

theorem savedBooleanValue_not_comparison (index negations : Nat) (argument : Option Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr negations (SavedBooleanGuard.reference index argument)) = none := by
  induction negations with
  | zero => cases argument <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem savedBooleanValue_not_closed (index negations : Nat) (argument : Option Lean.Expr) :
    booleanGuardOperands? (BooleanGuardNegation.expr negations (SavedBooleanGuard.reference index argument)) = none := by
  induction negations with
  | zero => cases argument <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

end LeanExe.Extract.Core
