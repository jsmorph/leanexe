import LeanExe.Source.ScalarGuard
import LeanExe.Extract.ScalarComparison

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (Guard CompoundGuard Junction Comparison)

def guardOperands? : Lean.Expr → Option Guard
  | .app (.app (.const ``And []) left) right => do
      let a ← guardOperands? left
      let b ← guardOperands? right
      pure (.junction .conjunction a b)
  | .app (.app (.const ``Or []) left) right => do
      let a ← guardOperands? left
      let b ← guardOperands? right
      pure (.junction .disjunction a b)
  | expression => (comparisonOperands? expression).map fun (op, a, b) => .compare op a b

@[simp] theorem guardOperands_compare (op : Comparison) (a b : Lean.Expr) :
    guardOperands? (op.condition a b) = some (.compare op a b) := by
  cases op <;> simp [Comparison.condition, Comparison.boolExpr, guardOperands?, comparisonOperands?]

@[simp] theorem guardOperands_condition (guard : Guard) :
    guardOperands? guard.condition = some guard := by
  induction guard with
  | compare op a b => exact guardOperands_compare op a b
  | junction op a b iha ihb =>
    cases op <;> simp [Guard.condition, Junction.condition, guardOperands?, iha, ihb]

theorem guardOperands_sound {expression : Lean.Expr} {guard : Guard}
    (parsed : guardOperands? expression = some guard) : expression = guard.condition := by
  induction expression using guardOperands?.induct generalizing guard with
  | case1 left right ihl ihr =>
    rw [guardOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [Guard.condition, Junction.condition, ihl ha, ihr hb]
  | case2 left right ihl ihr =>
    rw [guardOperands?] at parsed
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨a, ha, b, hb, rfl⟩ := parsed
    simp [Guard.condition, Junction.condition, ihl ha, ihr hb]
  | case3 expression excludedAnd excludedOr =>
    rw [guardOperands?] at parsed
    · obtain ⟨⟨op, a, b⟩, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact comparisonOperands_sound found
    · exact excludedAnd
    · exact excludedOr

/-- The complete tree's standard decision evidence is checked before admission. -/
def compoundGuard? (condition evidence : Lean.Expr) : Option CompoundGuard := do
  let .junction op left right ← guardOperands? condition | none
  let guard : CompoundGuard := ⟨op, left, right⟩
  if LeanExe.Source.ExprEquality.same evidence guard.evidence then some guard else none

@[simp] theorem compoundGuard_accepts (guard : CompoundGuard) :
    compoundGuard? guard.condition guard.evidence = some guard := by
  cases guard
  simp [compoundGuard?, CompoundGuard.tree]

theorem compoundGuard_sound {condition evidence : Lean.Expr} {guard : CompoundGuard}
    (parsed : compoundGuard? condition evidence = some guard) :
    condition = guard.condition ∧ evidence = guard.evidence := by
  unfold compoundGuard? at parsed
  simp only [bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨tree, found, accepted⟩ := parsed
  cases tree with
  | compare => contradiction
  | junction op left right =>
    change (if LeanExe.Source.ExprEquality.same evidence
        ({ junction := op, left, right } : CompoundGuard).evidence = true
      then some { junction := op, left, right } else none) = some guard at accepted
    split at accepted
    · rename_i same
      cases accepted
      exact ⟨guardOperands_sound found, LeanExe.Source.ExprEquality.same_eq_true.mp same⟩
    · contradiction

theorem compoundGuard_size {condition evidence : Lean.Expr} {guard : CompoundGuard}
    (parsed : compoundGuard? condition evidence = some guard) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf condition := by
  rw [(compoundGuard_sound parsed).1]
  exact guard.tree.operands_size member

@[simp] theorem compoundGuard_not_comparison (guard : CompoundGuard) :
    comparison? guard.condition guard.evidence = none := by
  rcases guard with ⟨op, a, b⟩
  cases op <;> rfl

end LeanExe.Extract.Core
