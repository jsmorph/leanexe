import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Extract.ScalarGuardSyntax

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

def booleanLocalOperands? : Lean.Expr → Option BooleanLocal
  | .app (.app (.const ``Bool.and []) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.junction 0 .conjunction a b)
  | .app (.app (.const ``Bool.or []) left) right => do
      let a ← booleanLocalOperands? left
      let b ← booleanLocalOperands? right
      pure (.junction 0 .disjunction a b)
  | .app (.const ``Bool.not []) inner => (booleanLocalOperands? inner).map BooleanLocal.negate
  | .const ``Bool.true [] => some (.literal 0 true)
  | .const ``Bool.false [] => some (.literal 0 false)
  | .bvar index => some (.var 0 index)
  | expression => (booleanComparisonOperands? expression).map fun (op, a, b) => .compare op a b

@[simp] theorem booleanLocalOperands_compare (op : BooleanComparison) (a b : Lean.Expr) :
    booleanLocalOperands? (op.expr a b) = some (.compare op a b) := by
  induction op with
  | negate op ih => simp [BooleanComparison.expr, booleanLocalOperands?, ih, BooleanLocal.negate]
  | _ => rfl

@[simp] theorem booleanLocalOperands_expr (guard : BooleanLocal) :
    booleanLocalOperands? guard.expr = some guard := by
  induction guard with
  | var n index =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | literal n value =>
    induction n with
    | zero => cases value <;> rfl
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih
  | compare op a b => exact booleanLocalOperands_compare op a b
  | junction n op a b iha ihb =>
    induction n with
    | zero => cases op <;> simp [BooleanLocal.expr, BooleanGuardNegation.expr,
        Junction.booleanExpr, booleanLocalOperands?, iha, ihb]
    | succ n ih =>
      simpa only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanLocalOperands?,
        Option.map_some, BooleanLocal.negate] using congrArg (Option.map BooleanLocal.negate) ih

theorem booleanLocalOperands_sound {expression : Lean.Expr} {guard : BooleanLocal}
    (parsed : booleanLocalOperands? expression = some guard) : expression = guard.expr := by
  induction expression using booleanLocalOperands?.induct generalizing guard with
  | case1 left right ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, Junction.booleanExpr, ihl ha, ihr hb]
  | case2 left right ihl ihr =>
    rw [booleanLocalOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [BooleanLocal.expr, BooleanGuardNegation.expr, Junction.booleanExpr, ihl ha, ihr hb]
  | case3 inner ih =>
    rw [booleanLocalOperands?] at parsed
    obtain ⟨guard, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rw [BooleanLocal.negate_expr, ih found]
  | case4 | case5 => cases parsed; rfl
  | case6 index => cases parsed; rfl
  | case7 expression excludedAnd excludedOr excludedNot excludedTrue excludedFalse excludedVar =>
    rw [booleanLocalOperands?] at parsed
    · obtain ⟨⟨op, a, b⟩, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact booleanComparisonOperands_sound found
    · exact excludedAnd
    · exact excludedOr
    · exact excludedNot
    · exact excludedTrue
    · exact excludedFalse
    · exact excludedVar

theorem booleanLocalOperands_size {expression : Lean.Expr} {value : BooleanLocal}
    (parsed : booleanLocalOperands? expression = some value) {operand : Lean.Expr}
    (member : operand ∈ value.operands) : sizeOf operand < sizeOf expression := by
  rw [booleanLocalOperands_sound parsed]
  exact value.operands_size member

theorem booleanGuardOperands_variable (n index : Nat) :
    booleanGuardOperands? (BooleanGuardNegation.expr n (.bvar index)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanGuardOperands?, ih]

theorem booleanGuardOperands_local_closed (value : BooleanLocal) {guard : BooleanGuard}
    (parsed : booleanGuardOperands? value.expr = some guard) : value.variables = [] := by
  induction value generalizing guard with
  | var n index => simp [BooleanLocal.expr, booleanGuardOperands_variable] at parsed
  | literal | compare => rfl
  | junction n op a b iha ihb =>
    induction n generalizing guard with
    | zero =>
      cases op <;> simp only [BooleanLocal.expr, BooleanGuardNegation.expr,
        Junction.booleanExpr, booleanGuardOperands?, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at parsed
      all_goals
        obtain ⟨left, hl, right, hr, _⟩ := parsed
        simp [BooleanLocal.variables, iha hl, ihb hr]
    | succ n ih =>
      simp only [BooleanLocal.expr, BooleanGuardNegation.expr, booleanGuardOperands?] at parsed
      obtain ⟨inner, found, _⟩ := Option.map_eq_some_iff.mp parsed
      exact ih found

theorem booleanGuardOperands_local_none (value : BooleanLocal) (nonempty : value.variables ≠ []) :
    booleanGuardOperands? value.expr = none := by
  cases parsed : booleanGuardOperands? value.expr with
  | none => rfl
  | some guard => exact False.elim (nonempty (booleanGuardOperands_local_closed value parsed))

theorem booleanComparisonOperands_variable (n index : Nat) :
    booleanComparisonOperands? (BooleanGuardNegation.expr n (.bvar index)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BooleanGuardNegation.expr, booleanComparisonOperands?, ih]

theorem booleanLocal_not_comparison (value : BooleanLocal) (nonempty : value.variables ≠ []) :
    comparisonOperands? value.condition = none := by
  cases value with
  | literal | compare => simp [BooleanLocal.variables] at nonempty
  | var n index =>
    cases n with
    | zero => rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanComparisonOperands_variable]
  | junction n op a b =>
    cases n with
    | zero => cases op <;> rfl
    | succ n => simp [BooleanLocal.condition, BooleanLocal.expr, BooleanGuardNegation.expr,
        comparisonOperands?, booleanJunction_not_comparison]

theorem booleanLocal_not_guard (guard : BooleanLocalGuard) :
    guardOperands? guard.condition = none := by
  have noComparison := booleanLocal_not_comparison guard.value guard.nonempty
  have noClosed := booleanGuardOperands_local_none guard.value guard.nonempty
  simp only [BooleanLocal.condition] at noComparison
  rw [guardOperands?]
  · simp [noComparison, booleanGuardCondition?, BooleanLocal.condition, noClosed]
  all_goals simp [BooleanLocalGuard.condition, BooleanLocal.condition]

theorem booleanLocal_not_compound (guard : BooleanLocalGuard) :
    compoundGuard? guard.condition guard.evidence = none := by
  simp [compoundGuard?, compoundGuardShape?, booleanLocal_not_guard]

def booleanLocalCondition? : Lean.Expr → Option BooleanLocal
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) expression) (.const ``Bool.true []) =>
      booleanLocalOperands? expression
  | _ => none

theorem booleanLocalCondition_sound {condition : Lean.Expr} {value : BooleanLocal}
    (parsed : booleanLocalCondition? condition = some value) : condition = value.condition := by
  unfold booleanLocalCondition? at parsed
  split at parsed
  · rename_i expression
    rw [booleanLocalOperands_sound parsed]
    rfl
  · contradiction

def booleanLocalGuard? (condition evidence : Lean.Expr) : Option BooleanLocalGuard := do
  let value ← booleanLocalCondition? condition
  if nonempty : value.variables ≠ [] then
    if LeanExe.Source.ExprEquality.same evidence value.evidence then some ⟨value, nonempty⟩ else none
  else none

@[simp] theorem booleanLocalGuard_accepts (guard : BooleanLocalGuard) :
    booleanLocalGuard? guard.condition guard.evidence = some guard := by
  cases guard with
  | mk value nonempty =>
    simp [booleanLocalGuard?, booleanLocalCondition?, BooleanLocalGuard.condition, BooleanLocal.condition,
      BooleanLocalGuard.evidence, nonempty]

theorem booleanLocalGuard_sound {condition evidence : Lean.Expr} {guard : BooleanLocalGuard}
    (parsed : booleanLocalGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  simp only [booleanLocalGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨value, matched, accepted⟩ := parsed
  split at accepted
  · split at accepted
    · rename_i same
      cases accepted
      exact ⟨booleanLocalCondition_sound matched, LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
    · contradiction
  · contradiction

theorem booleanLocalGuard_not_comparison (guard : BooleanLocalGuard) :
    comparison? guard.condition guard.evidence = none := by
  simp [comparison?, booleanLocal_not_comparison guard.value guard.nonempty]

theorem booleanLocalGuard_size {condition evidence : Lean.Expr} {guard : BooleanLocalGuard}
    (parsed : booleanLocalGuard? condition evidence = some guard) {operand : Lean.Expr}
    (member : operand ∈ guard.value.operands) : sizeOf operand < sizeOf condition := by
  rw [(booleanLocalGuard_sound parsed).1]
  have bound := guard.value.operands_size member
  simp only [BooleanLocalGuard.condition, BooleanLocal.condition]
  simp_all; omega

end LeanExe.Extract.Core
