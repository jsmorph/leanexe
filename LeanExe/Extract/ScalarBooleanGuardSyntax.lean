import LeanExe.Source.ScalarBooleanGuard
import LeanExe.Extract.ScalarComparison

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

def booleanGuardOperands? : Lean.Expr → Option BooleanGuard
  | .app (.app (.const ``Bool.and []) left) right => do
      let a ← booleanGuardOperands? left
      let b ← booleanGuardOperands? right
      pure (.junction 0 .conjunction a b)
  | .app (.app (.const ``Bool.or []) left) right => do
      let a ← booleanGuardOperands? left
      let b ← booleanGuardOperands? right
      pure (.junction 0 .disjunction a b)
  | .app (.const ``Bool.not []) inner => (booleanGuardOperands? inner).map BooleanGuard.negate
  | expression => (booleanComparisonOperands? expression).map fun (op, a, b) => .compare op a b

@[simp] theorem booleanGuardOperands_compare (op : BooleanComparison) (a b : Lean.Expr) :
    booleanGuardOperands? (op.expr a b) = some (.compare op a b) := by
  induction op with
  | negate op ih => simp [BooleanComparison.expr, booleanGuardOperands?, ih, BooleanGuard.negate]
  | _ => rfl

@[simp] theorem booleanGuardOperands_expr (guard : BooleanGuard) :
    booleanGuardOperands? guard.expr = some guard := by
  induction guard with
  | compare op a b => exact booleanGuardOperands_compare op a b
  | junction n op a b iha ihb =>
    induction n with
    | zero => cases op <;> simp [BooleanGuard.expr, BooleanGuardNegation.expr,
        Junction.booleanExpr, booleanGuardOperands?, iha, ihb]
    | succ n ih =>
      simpa only [BooleanGuard.expr, BooleanGuardNegation.expr, booleanGuardOperands?,
        Option.map_some, BooleanGuard.negate] using congrArg (Option.map BooleanGuard.negate) ih

theorem booleanGuardOperands_sound {expression : Lean.Expr} {guard : BooleanGuard}
    (parsed : booleanGuardOperands? expression = some guard) : expression = guard.expr := by
  induction expression using booleanGuardOperands?.induct generalizing guard with
  | case1 left right ihl ihr =>
    rw [booleanGuardOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanGuard.expr, BooleanGuardNegation.expr, Junction.booleanExpr, ihl ha, ihr hb]
  | case2 left right ihl ihr =>
    rw [booleanGuardOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanGuard.expr, BooleanGuardNegation.expr, Junction.booleanExpr, ihl ha, ihr hb]
  | case3 inner ih =>
    rw [booleanGuardOperands?] at parsed
    obtain ⟨guard, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rw [BooleanGuard.negate_expr, ih found]
  | case4 expression excludedAnd excludedOr excludedNot =>
    rw [booleanGuardOperands?] at parsed
    · obtain ⟨⟨op, a, b⟩, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact booleanComparisonOperands_sound found
    · exact excludedAnd
    · exact excludedOr
    · exact excludedNot

theorem booleanJunction_not_comparison (n : Nat) (op : Junction) (a b : Lean.Expr) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (op.booleanExpr a b)) = none := by
  induction n with
  | zero => cases op <;> rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

def booleanGuardCondition? : Lean.Expr → Option BooleanGuard
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) inner) (.const ``Bool.true []) =>
      booleanGuardOperands? inner
  | _ => none

@[simp] theorem booleanGuardCondition_accepts (guard : BooleanGuard) :
    booleanGuardCondition? guard.condition = some guard := by
  simp [booleanGuardCondition?, BooleanGuard.condition]

theorem booleanGuardCondition_sound {condition : Lean.Expr} {guard : BooleanGuard}
    (parsed : booleanGuardCondition? condition = some guard) : condition = guard.condition := by
  unfold booleanGuardCondition? at parsed
  split at parsed
  · rename_i inner
    rw [booleanGuardOperands_sound parsed]
    rfl
  · contradiction

theorem booleanJunction_condition_not_comparison (n : Nat) (op : Junction) (a b : BooleanGuard) :
    comparisonOperands? (BooleanGuard.junction n op a b).condition = none := by
  cases n with
  | zero => cases op <;> rfl
  | succ n =>
    simp [BooleanGuard.condition, BooleanGuard.expr, BooleanGuardNegation.expr,
      comparisonOperands?, booleanJunction_not_comparison]

end LeanExe.Extract.Core
