import LeanExe.Source.ScalarCompoundGuard
import LeanExe.Extract.ScalarBooleanGuardSyntax
import LeanExe.Extract.ScalarComparison

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar

def guardOperands? : Lean.Expr → Option Guard
  | .app (.app (.const ``And []) left) right => do
      let a ← guardOperands? left
      let b ← guardOperands? right
      pure (.junction 0 .conjunction a b)
  | .app (.app (.const ``Or []) left) right => do
      let a ← guardOperands? left
      let b ← guardOperands? right
      pure (.junction 0 .disjunction a b)
  | .app (.const ``Not []) inner => (guardOperands? inner).map Guard.negate
  | expression => (comparisonOperands? expression).map fun (op, a, b) => .compare op a b

@[simp] theorem guardOperands_compare (op : Comparison) (a b : Lean.Expr) :
    guardOperands? (op.condition a b) = some (.compare op a b) := by
  induction op with
  | negate op ih => simp [Comparison.condition, guardOperands?, ih, Guard.negate]
  | _ => simp [Comparison.condition, Comparison.boolExpr, guardOperands?, comparisonOperands?]

@[simp] theorem guardOperands_condition (guard : Guard) :
    guardOperands? guard.condition = some guard := by
  induction guard with
  | compare op a b => exact guardOperands_compare op a b
  | junction n op a b iha ihb =>
    induction n with
    | zero => cases op <;> simp [Guard.condition, GuardNegation.condition, Junction.condition, guardOperands?, iha, ihb]
    | succ n ih =>
      simpa only [Guard.condition, GuardNegation.condition, guardOperands?, Option.map_some, Guard.negate] using
        congrArg (Option.map Guard.negate) ih

theorem guardOperands_sound {expression : Lean.Expr} {guard : Guard}
    (parsed : guardOperands? expression = some guard) : expression = guard.condition := by
  induction expression using guardOperands?.induct generalizing guard with
  | case1 left right ihl ihr =>
    rw [guardOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [Guard.condition, GuardNegation.condition, Junction.condition, ihl ha, ihr hb]
  | case2 left right ihl ihr =>
    rw [guardOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [Guard.condition, GuardNegation.condition, Junction.condition, ihl ha, ihr hb]
  | case3 inner ih =>
    rw [guardOperands?] at parsed
    obtain ⟨guard, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rw [Guard.negate_condition, ih found]
  | case4 expression excludedAnd excludedOr excludedNot =>
    rw [guardOperands?] at parsed
    · obtain ⟨⟨op, a, b⟩, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact comparisonOperands_sound found
    · exact excludedAnd
    · exact excludedOr
    · exact excludedNot

theorem junction_not_comparison (n : Nat) (op : Junction) (a b : Lean.Expr) :
    comparisonOperands? (GuardNegation.condition n (op.condition a b)) = none := by
  induction n with
  | zero => cases op <;> rfl
  | succ n ih => simp [GuardNegation.condition, comparisonOperands?, ih]

theorem booleanJunction_condition_not_comparison (n : Nat) (op : Junction) (a b : BooleanGuard) :
    comparisonOperands? (BooleanGuard.junction n op a b).condition = none := by
  cases n with
  | zero => cases op <;> rfl
  | succ n =>
    simp [BooleanGuard.condition, BooleanGuard.expr, BooleanGuardNegation.expr,
      comparisonOperands?, booleanJunction_not_comparison]

theorem booleanJunction_not_proposition (n : Nat) (op : Junction) (a b : BooleanGuard) :
    guardOperands? (BooleanGuard.junction n op a b).condition = none := by
  change (comparisonOperands? (BooleanGuard.junction n op a b).condition).map _ = none
  rw [booleanJunction_condition_not_comparison]
  rfl

def booleanCompoundGuardShape? : Lean.Expr → Option CompoundGuard
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) inner) (.const ``Bool.true []) => do
      let .junction n op a b ← booleanGuardOperands? inner | none
      pure (.boolean op a b n)
  | _ => none

theorem booleanCompoundGuardShape_sound {condition : Lean.Expr} {guard : CompoundGuard}
    (parsed : booleanCompoundGuardShape? condition = some guard) : condition = guard.condition := by
  unfold booleanCompoundGuardShape? at parsed
  split at parsed
  · rename_i inner
    simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨tree, found, accepted⟩ := parsed
    cases tree with
    | compare => contradiction
    | junction n op a b =>
      cases accepted
      change _ = (BooleanGuard.junction n op a b).condition
      rw [booleanGuardOperands_sound found]
      rfl
  · contradiction

def compoundGuardShape? (condition : Lean.Expr) : Option CompoundGuard :=
  match guardOperands? condition with
  | some (.junction n op a b) => some (.proposition op a b n)
  | _ => booleanCompoundGuardShape? condition

@[simp] theorem compoundGuardShape_accepts (guard : CompoundGuard) :
    compoundGuardShape? guard.condition = some guard := by
  cases guard with
  | proposition op a b n =>
    simp [compoundGuardShape?, CompoundGuard.condition]
  | boolean op a b n =>
    simp only [compoundGuardShape?, CompoundGuard.condition, booleanJunction_not_proposition]
    simp [booleanCompoundGuardShape?, BooleanGuard.condition, booleanGuardOperands_expr]

theorem compoundGuardShape_sound {condition : Lean.Expr} {guard : CompoundGuard}
    (parsed : compoundGuardShape? condition = some guard) : condition = guard.condition := by
  unfold compoundGuardShape? at parsed
  split at parsed
  · rename_i n op a b found
    cases parsed
    exact guardOperands_sound found
  · exact booleanCompoundGuardShape_sound parsed

/-- Check the entire decision expression for either admitted compound form. -/
def compoundGuard? (condition evidence : Lean.Expr) : Option CompoundGuard := do
  let guard ← compoundGuardShape? condition
  if LeanExe.Source.ExprEquality.same evidence guard.evidence then some guard else none

@[simp] theorem compoundGuard_accepts (guard : CompoundGuard) :
    compoundGuard? guard.condition guard.evidence = some guard := by
  simp [compoundGuard?]

theorem compoundGuard_sound {condition evidence : Lean.Expr} {guard : CompoundGuard}
    (parsed : compoundGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  simp only [compoundGuard?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨shape, found, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨compoundGuardShape_sound found, LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
  · contradiction

theorem compoundGuard_size {condition evidence : Lean.Expr} {guard : CompoundGuard}
    (parsed : compoundGuard? condition evidence = some guard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf condition := by
  rw [(compoundGuard_sound parsed).1]
  exact guard.operands_size member

@[simp] theorem compoundGuard_not_comparison (guard : CompoundGuard) :
    comparison? guard.condition guard.evidence = none := by
  cases guard with
  | proposition op a b n =>
    simp [comparison?, CompoundGuard.condition, Guard.condition, junction_not_comparison]
  | boolean op a b n =>
    simp [comparison?, CompoundGuard.condition, booleanJunction_condition_not_comparison]

end LeanExe.Extract.Core
