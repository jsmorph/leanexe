import LeanExe.Extract.ScalarGuardSyntax
import LeanExe.Extract.ScalarBooleanGuard

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (Guard CompoundGuard BooleanGuard)

/-- The callback only receives operands of this exact parsed guard. Membership
allows the surrounding source compiler to prove its recursive calls decrease. -/
def extractGuard : (guard : Guard) →
    ((operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr) → Option LeanExe.IR.Cond
  | .compare op a b, compile => do
      let left ← compile a (by simp [Guard.operands])
      let right ← compile b (by simp [Guard.operands])
      pure (lowerComparison op left right)
  | .junction n op a b, compile => do
      let left ← extractGuard a (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractGuard b (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerJunction op left right))
  | .boolean m n op a b, compile => do
      let condition ← extractBooleanGuard (.junction n op a b) compile
      pure (lowerGuardNegations m condition)

theorem extractGuard_accepts (guard : Guard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (total : ∀ operand member, ∃ target, compile operand member = some target) :
    ∃ target, extractGuard guard compile = some target := by
  induction guard with
  | compare op a b =>
    obtain ⟨left, hl⟩ := total a (by simp [Guard.operands])
    obtain ⟨right, hr⟩ := total b (by simp [Guard.operands])
    exact ⟨lowerComparison op left right, by simp [extractGuard, hl, hr]⟩
  | junction n op a b iha ihb =>
    obtain ⟨left, hl⟩ := iha (fun operand member => compile operand (List.mem_append_left _ member))
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (fun operand member => compile operand (List.mem_append_right _ member))
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractGuard, hl, hr]⟩
  | boolean m n op a b =>
    obtain ⟨condition, hc⟩ := extractBooleanGuard_accepts (.junction n op a b) compile total
    exact ⟨lowerGuardNegations m condition, by simp [extractGuard, hc]⟩

theorem extractGuard_operands (guard : Guard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractGuard guard compile = some target) :
    ∀ operand member, ∃ expression, compile operand member = some expression := by
  induction guard generalizing target with
  | compare op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    simp only [Guard.operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨left, hl⟩
    · exact ⟨right, hr⟩
  | junction n op a b iha ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | second
    · exact iha _ hl operand first
    · exact ihb _ hr operand second
  | boolean m n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact extractBooleanGuard_operands (.junction n op a b) compile hc

theorem extractGuard_correct (guard : Guard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (native : Lean.Expr → UInt64) {target : LeanExe.IR.Cond} {store : LeanExe.IR.ScalarStore}
    (compiled : extractGuard guard compile = some target)
    (meanings : ∀ operand member expression, compile operand member = some expression →
      expression.ScalarEval store (native operand) store) :
    target.ScalarEval store (guard.denote native) store := by
  induction guard generalizing target with
  | compare op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerComparison_correct op (meanings _ _ _ hl) (meanings _ _ _ hr)
  | junction n op a b iha ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerJunction_correct op
      (iha _ hl (fun operand member expression found => meanings _ _ _ found))
      (ihb _ hr (fun operand member expression found => meanings _ _ _ found)))
  | boolean m n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_correct m
      (extractBooleanGuard_correct (.junction n op a b) compile native hc meanings)

theorem extractGuard_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (guard : Guard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractGuard guard compile = some target)
    (operands : ∀ operand member expression, compile operand member = some expression → P expression) :
    ∀ t e, P t → P e → P (.ite target t e) := by
  induction guard generalizing target with
  | compare op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact fun t e ht he => choice op _ _ _ _ (operands _ _ _ hl) (operands _ _ _ hr) ht he
  | junction n op a b iha ihb =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerJunction_choice P literal binary choice op left right
        (iha _ hl (fun operand member expression found => operands _ _ _ found))
        (ihb _ hr (fun operand member expression found => operands _ _ _ found)))
  | boolean m n op a b =>
    simp only [extractGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice m _
      (extractBooleanGuard_choice P literal binary choice (.junction n op a b) compile hc operands)

end LeanExe.Extract.Core
