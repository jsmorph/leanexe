import LeanExe.Extract.ScalarGuardLowering

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (BooleanGuard)

/-- The callback only receives operands of this exact parsed guard. Membership
allows the surrounding source compiler to prove its recursive calls decrease. -/
def extractBooleanGuard : (guard : BooleanGuard) →
    ((operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr) → Option LeanExe.IR.Cond
  | .literal n value, _ => some (lowerGuardLiteral (LeanExe.Source.Scalar.GuardNegation.denote n value))
  | .compare op a b, compile => do
      let left ← compile a (by simp [BooleanGuard.operands])
      let right ← compile b (by simp [BooleanGuard.operands])
      pure (lowerComparison (BooleanGuard.comparison op) left right)
  | .junction n op a b, compile => do
      let left ← extractBooleanGuard a (fun operand member => compile operand (List.mem_append_left _ member))
      let right ← extractBooleanGuard b (fun operand member => compile operand (List.mem_append_right _ member))
      pure (lowerGuardNegations n (lowerJunction op left right))

theorem extractBooleanGuard_accepts (guard : BooleanGuard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (total : ∀ operand member, ∃ target, compile operand member = some target) :
    ∃ target, extractBooleanGuard guard compile = some target := by
  induction guard with
  | literal n value => exact ⟨_, rfl⟩
  | compare op a b =>
    obtain ⟨left, hl⟩ := total a (by simp [BooleanGuard.operands])
    obtain ⟨right, hr⟩ := total b (by simp [BooleanGuard.operands])
    exact ⟨lowerComparison (BooleanGuard.comparison op) left right, by simp [extractBooleanGuard, hl, hr]⟩
  | junction n op a b iha ihb =>
    obtain ⟨left, hl⟩ := iha (fun operand member => compile operand (List.mem_append_left _ member))
      (fun operand member => total operand _)
    obtain ⟨right, hr⟩ := ihb (fun operand member => compile operand (List.mem_append_right _ member))
      (fun operand member => total operand _)
    exact ⟨lowerGuardNegations n (lowerJunction op left right), by simp [extractBooleanGuard, hl, hr]⟩

theorem extractBooleanGuard_operands (guard : BooleanGuard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanGuard guard compile = some target) :
    ∀ operand member, ∃ expression, compile operand member = some expression := by
  induction guard generalizing target with
  | literal n value =>
    intro operand member
    simp [BooleanGuard.operands] at member
  | compare op a b =>
    simp only [extractBooleanGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    simp only [BooleanGuard.operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨left, hl⟩
    · exact ⟨right, hr⟩
  | junction n op a b iha ihb =>
    simp only [extractBooleanGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | second
    · exact iha _ hl operand first
    · exact ihb _ hr operand second

theorem extractBooleanGuard_correct (guard : BooleanGuard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    (native : Lean.Expr → UInt64) {target : LeanExe.IR.Cond} {store : LeanExe.IR.ScalarStore}
    (compiled : extractBooleanGuard guard compile = some target)
    (meanings : ∀ operand member expression, compile operand member = some expression →
      expression.ScalarEval store (native operand) store) :
    target.ScalarEval store (guard.denote native) store := by
  induction guard generalizing target with
  | literal n value =>
    simp only [extractBooleanGuard, Option.some.injEq] at compiled
    subst target
    exact lowerGuardLiteral_correct _ _
  | compare op a b =>
    simp only [extractBooleanGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    simpa only [BooleanGuard.denote, BooleanGuard.comparison_denote] using
      lowerComparison_correct (BooleanGuard.comparison op) (meanings _ _ _ hl) (meanings _ _ _ hr)
  | junction n op a b iha ihb =>
    simp only [extractBooleanGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_correct n (lowerJunction_correct op
      (iha _ hl (fun operand member expression found => meanings _ _ _ found))
      (ihb _ hr (fun operand member expression found => meanings _ _ _ found)))

theorem extractBooleanGuard_choice (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (binary : ∀ p a b, P a → P b → P (ScalarPrimitive.lower p a b))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (guard : BooleanGuard)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanGuard guard compile = some target)
    (operands : ∀ operand member expression, compile operand member = some expression → P expression) :
    ∀ t e, P t → P e → P (.ite target t e) := by
  induction guard generalizing target with
  | literal n value =>
    simp only [extractBooleanGuard, Option.some.injEq] at compiled
    subst target
    exact lowerGuardLiteral_choice P literal choice _
  | compare op a b =>
    simp only [extractBooleanGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact fun t e ht he => choice (BooleanGuard.comparison op) _ _ _ _ (operands _ _ _ hl) (operands _ _ _ hr) ht he
  | junction n op a b iha ihb =>
    simp only [extractBooleanGuard, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, rfl⟩ := compiled
    exact lowerGuardNegations_choice P literal choice n _
      (lowerJunction_choice P literal binary choice op left right
        (iha _ hl (fun operand member expression found => operands _ _ _ found))
        (ihb _ hr (fun operand member expression found => operands _ _ _ found)))

end LeanExe.Extract.Core
