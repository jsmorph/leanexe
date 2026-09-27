import LeanExe.Source.ScalarSavedBooleanGuard
import LeanExe.Extract.ScalarBooleanGuardSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem savedBooleanValue_not_closed (guard : SavedBooleanGuard) :
    booleanGuardOperands? guard.expr = none := by
  cases found : booleanGuardOperands? guard.expr with
  | none => rfl
  | some closed => exact False.elim (guard.extended closed (booleanGuardOperands_sound found))

def savedBooleanGuard? : Lean.Expr → Option SavedBooleanGuard
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value) (.const ``Bool.true []) =>
      if excluded : booleanGuardOperands? value = none then
        some ⟨value, fun closed same => by
          rw [same, booleanGuardOperands_expr] at excluded
          contradiction⟩
      else none
  | _ => none

@[simp] theorem savedBooleanGuard_accepts (guard : SavedBooleanGuard) :
    savedBooleanGuard? guard.condition = some guard := by
  obtain ⟨value, extended⟩ := guard
  have excluded := savedBooleanValue_not_closed ⟨value, extended⟩
  change booleanGuardOperands? value = none at excluded
  simp [SavedBooleanGuard.condition, SavedBooleanGuard.expr, savedBooleanGuard?, excluded]

theorem savedBooleanGuard_sound {condition : Lean.Expr} {guard : SavedBooleanGuard}
    (parsed : savedBooleanGuard? condition = some guard) : condition = guard.condition := by
  unfold savedBooleanGuard? at parsed
  split at parsed
  · split at parsed
    · cases parsed; rfl
    · contradiction
  · contradiction

theorem booleanTruth_not_comparison_of_not_closed (value : Lean.Expr)
    (extended : ∀ guard : BooleanGuard, value ≠ guard.expr) :
    comparisonOperands? (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value)
      (.const ``Bool.true [])) = none := by
  cases found : comparisonOperands? (.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value)
      (.const ``Bool.true [])) with
  | none => rfl
  | some result =>
    obtain ⟨op, a, b⟩ := result
    have shape := comparisonOperands_sound found
    cases op with
    | eq type | ne type | lt type | le type | gt type | ge type =>
      cases type <;> simp [Comparison.condition, ResultType.expr] at shape
    | negate op => simp [Comparison.condition] at shape
    | beq =>
      have same : value = (BooleanGuard.compare .eq a b).expr := by
        simpa [Comparison.condition, Comparison.boolExpr, BooleanGuard.expr,
          BooleanComparison.expr, BooleanComparison.atom] using shape
      exact False.elim (extended _ same)
    | bne =>
      have same : value = (BooleanGuard.compare .ne a b).expr := by
        simpa [Comparison.condition, Comparison.boolExpr, BooleanGuard.expr,
          BooleanComparison.expr, BooleanComparison.atom] using shape
      exact False.elim (extended _ same)
    | boolNot op =>
      have same : value = (BooleanGuard.compare (.negate op) a b).expr := by
        simpa [Comparison.condition, BooleanGuard.expr, BooleanComparison.expr] using shape
      exact False.elim (extended _ same)

end LeanExe.Extract.Core
